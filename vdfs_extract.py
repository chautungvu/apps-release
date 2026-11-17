#!/usr/bin/env python3
"""
vdfs_extract.py - read-only extractor for VDFS4 images (Samsung / Tizen).

Reads a raw VDFS4 image (such as platform.img) directly, without the kernel
driver. Layout knowledge comes from the GPL vdfs4-tools sources.

Usage:
    python vdfs_extract.py IMAGE --info
    python vdfs_extract.py IMAGE --list [--path /some/dir]
    python vdfs_extract.py IMAGE --extract OUTDIR [--path /some/dir] [--verbose]

Notes:
  * Signatures / hashes are NOT verified (this is a plain reader).
  * Encrypted files (VDFS4_ENCRYPTED_FILE) cannot be decrypted without the key;
    they are reported and skipped.
  * Python 3.7+. For zstd-compressed files: pip install zstandard
"""
import argparse
import csv
import os
import stat as stat_mod
import struct
import sys
import zlib

# ---------------------------------------------------------------- constants
SB_OFFSETS = [(0x200, 0x400, 0x600), (0x1200, 0x1400, 0x1600)]  # (sb1, sb, exsb)
SF_NR = 5                       # special files with translation tables
INO_ROOT, INO_CAT, INO_SPACE, INO_EXT, INO_INOBMP, INO_XATTR = 1, 2, 3, 4, 5, 6

REC_FOLDER, REC_FILE, REC_HLINK, REC_ILINK = 1, 2, 3, 5

# catalog record flag bit numbers (1 << n)
F_HAS_BLOCKS_IN_EXTTREE = 1
F_HARD_LINK = 10
F_COMPRESSED = 13
F_ENCRYPTED = 17
F_INLINE = 19
F_COMP_INLINE = 20

NODE_INDEX, NODE_LEAF = 1, 2


class VdfsError(Exception):
    pass


def bit(flags, n):
    return bool(flags & (1 << n))


# ---------------------------------------------------------------- LZO1X
def lzo1x_decompress(src, expected_len=None):
    """Pure-python LZO1X decompressor (port of the Linux kernel algorithm)."""
    try:
        import lzo  # python-lzo, if the user has it (much faster)
        if expected_len:
            return lzo.decompress(bytes(src), False, expected_len)
    except Exception:
        pass
    src = bytes(src)
    n = len(src)
    out = bytearray()
    ip = 0
    state = 0
    nxt = 0

    def zero_ext(ip, t, base):
        while src[ip] == 0:
            t += 255
            ip += 1
        t += base + src[ip]
        return ip + 1, t

    if n == 0:
        return b""
    if src[0] > 17:
        t = src[0] - 17
        ip = 1
        if t < 4:
            nxt = t
            out += src[ip:ip + t]
            ip += t
            state = nxt
        else:
            out += src[ip:ip + t]
            ip += t
            state = 4
    while True:
        if ip >= n:
            raise VdfsError("lzo: input overrun")
        t = src[ip]
        ip += 1
        m = None
        if t < 16:
            if state == 0:
                if t == 0:
                    ip, t = zero_ext(ip, 0, 15)
                t += 3
                out += src[ip:ip + t]
                ip += t
                state = 4
                continue
            elif state != 4:
                nxt = t & 3
                m = len(out) - 1 - (t >> 2) - (src[ip] << 2)
                ip += 1
                tl = 0  # copy 2 bytes
                for _ in range(2):
                    out.append(out[m]); m += 1
                state = nxt
                out += src[ip:ip + nxt]
                ip += nxt
                continue
            else:
                nxt = t & 3
                m = len(out) - 0x801 - (t >> 2) - (src[ip] << 2)
                ip += 1
                for _ in range(3):
                    out.append(out[m]); m += 1
                state = nxt
                out += src[ip:ip + nxt]
                ip += nxt
                continue
        elif t >= 64:
            nxt = t & 3
            m = len(out) - 1 - ((t >> 2) & 7) - (src[ip] << 3)
            ip += 1
            t = (t >> 5) - 1
        elif t >= 32:
            t &= 31
            if t == 0:
                ip, t = zero_ext(ip, 0, 31)
            w = src[ip] | (src[ip + 1] << 8)
            ip += 2
            m = len(out) - 1 - (w >> 2)
            nxt = w & 3
        else:
            m = len(out) - ((t & 8) << 11)
            t &= 7
            if t == 0:
                ip, t = zero_ext(ip, 0, 7)
            w = src[ip] | (src[ip + 1] << 8)
            ip += 2
            m -= (w >> 2)
            nxt = w & 3
            if m == len(out):
                break  # end-of-stream marker
            m -= 0x4000
        if m < 0:
            raise VdfsError("lzo: lookbehind overrun")
        for _ in range(t + 2):
            out.append(out[m]); m += 1
        state = nxt
        out += src[ip:ip + nxt]
        ip += nxt
    return bytes(out)


def decompress_chunk(kind, data, out_len):
    if kind == "Zip":
        return zlib.decompressobj().decompress(data)
    if kind == "Gzp":
        return zlib.decompressobj(31).decompress(data)
    if kind == "Lzo":
        return lzo1x_decompress(data, out_len)
    if kind == "Zst":
        try:
            import zstandard
        except ImportError:
            raise VdfsError("zstd-compressed data found; run: pip install zstandard")
        return zstandard.ZstdDecompressor().decompress(data, max_output_size=max(out_len, 1))
    raise VdfsError("unknown compression type %r" % (kind,))


# ---------------------------------------------------------------- image
class Entry:
    __slots__ = ("object_id", "parent_id", "name", "rtype", "mode", "uid", "gid",
                 "mtime", "flags", "size", "fork", "links", "items")

    def __repr__(self):
        return "<Entry %s id=%d parent=%d>" % (self.name, self.object_id, self.parent_id)


class Vdfs:
    def __init__(self, path, strict=True):
        self.path = path
        self.f = open(path, "rb")
        self.f.seek(0, 2)
        self.file_size = self.f.tell()
        self.strict = strict
        self.warnings = []
        self._read_super()
        self._read_snapshot()

    # ---- low level
    def read_at(self, off, n):
        self.f.seek(off)
        b = self.f.read(n)
        if len(b) != n:
            b = b + b"\0" * (n - len(b)) if not self.strict else b
            if len(b) != n:
                raise VdfsError("short read at 0x%x (+%d): image truncated?" % (off, n))
        return b

    def warn(self, msg):
        if len(self.warnings) < 200:
            self.warnings.append(msg)

    # ---- superblocks
    def _read_super(self):
        errs = []
        for sb1, sb, exsb in SB_OFFSETS:
            head = self.read_at(sb, 512)
            if head[:4] != b"VDFS":
                errs.append("no VDFS signature at 0x%x" % sb)
                continue
            self.sb_raw = head
            self.layout_version = head[4:8].decode("ascii", "replace")
            self.max_blocks, = struct.unpack_from("<Q", head, 8)
            self.volume_name = head[0x2C:0x3C].split(b"\0")[0].decode("ascii", "replace")
            self.mkfs_version = head[0x3C:0x7C].split(b"\0")[0].decode("ascii", "replace")
            (self.log_block, self.log_super_page, self.log_erase, self.case_insens,
             self.read_only, self.crc_present, self.force_full, self.hash_type,
             self.enc_flags, self.sign_type) = head[0xA4:0xAE]
            self.inode_count, = struct.unpack_from("<Q", head, 0xF0)
            self.block_size = 1 << self.log_block
            self.bnode_size = 1 << self.log_super_page
            e = self.read_at(exsb, 0xA00)
            self.exsb_raw = e
            self.files_count, self.folders_count = struct.unpack_from("<QQ", e, 0)
            self.volume_body = struct.unpack_from("<QQ", e, 0x10)
            self.meta_tbc, = struct.unpack_from("<I", e, 0x40)
            self.tables_ext = struct.unpack_from("<QQ", e, 0x48)
            self.meta_extents = []
            for i in range(96):
                b, l = struct.unpack_from("<QQ", e, 0x58 + 16 * i)
                if l:
                    self.meta_extents.append((b, l))
            self.volume_blocks, = struct.unpack_from("<Q", e, 0x668)
            self.exsb_crc_flag = e[0x670]
            if self.layout_version not in ("2006", "2007"):
                self.warn("unexpected layout version %s" % self.layout_version)
            if self.block_size != 4096:
                self.warn("unusual block size %d" % self.block_size)
            if self.enc_flags & 1:
                self.warn("volume flagged as encrypted: file contents may be unreadable")
            return
        raise VdfsError("not a VDFS4 image (%s)" % "; ".join(errs))

    # ---- snapshot (translation) tables
    def _read_snapshot(self):
        first, length = self.tables_ext
        bs = self.block_size
        best = None
        # The tables area holds two copies when the image is read-write.
        for copy_idx in (0, 1):
            half = length // 2
            off = (first + copy_idx * half) * bs
            if off >= self.file_size:
                continue
            hdr = self.read_at(off, 24 + 16 * SF_NR)
            if hdr[:4] != b"CoWB":
                continue
            sync, = struct.unpack_from("<I", hdr, 4)
            mount, = struct.unpack_from("<Q", hdr, 8)
            csum_off, = struct.unpack_from("<Q", hdr, 16)
            key = (mount, sync)
            if best is None or key > best[0]:
                best = (key, off, csum_off)
        if best is None:
            # single copy fallback
            off = first * bs
            hdr = self.read_at(off, 24)
            if hdr[:4] != b"CoWB":
                raise VdfsError("no CoWB snapshot table at block %d" % first)
            csum_off, = struct.unpack_from("<Q", hdr, 16)
            best = ((0, 0), off, csum_off)
        _, off, csum_off = best
        self.table_off = off
        if csum_off > 64 * 1024 * 1024:
            raise VdfsError("bad snapshot table size")
        self.base = self.read_at(off, csum_off + 4)
        stored = struct.unpack_from("<I", self.base, csum_off)[0]
        calc = (zlib.crc32(self.base[:csum_off], 0xFFFFFFFF) ^ 0xFFFFFFFF) & 0xFFFFFFFF  # vdfs4_crc32: init 0, no final xor
        self.base_crc_ok = (stored == calc)
        self.last_page_index = struct.unpack_from("<%dQ" % SF_NR, self.base, 24)
        self.table_offsets = struct.unpack_from("<%dQ" % SF_NR, self.base, 24 + 8 * SF_NR)
        # extended tables (CoW updates), applied on top of the base table
        self.overrides = {}  # (ino, node_id) -> meta_iblock
        pos = (csum_off + 4 + 4095) & ~4095
        for _ in range(64):
            try:
                eh = self.read_at(off + pos, 32)
            except VdfsError:
                break
            if eh[:4] != b"CoWE":
                break
            e_csum, = struct.unpack_from("<Q", eh, 16)
            rec_count, = struct.unpack_from("<I", eh, 24)
            if e_csum > 64 * 1024 * 1024 or rec_count > 10_000_000:
                break
            body = self.read_at(off + pos + 32, rec_count * 24)
            for i in range(rec_count):
                obj, idx, miblock = struct.unpack_from("<QQQ", body, 24 * i)
                self.overrides[(obj, idx)] = miblock
            pos = (pos + e_csum + 4 + 4095) & ~4095

    def table_record(self, ino, node_id):
        """-> (meta_iblock, sync, mount) for node `node_id` of tree `ino`"""
        idx = ino - INO_CAT
        n_rec = self.last_page_index[idx] + 1
        if node_id >= n_rec:
            raise VdfsError("node %d beyond table of tree %d (%d records)" % (node_id, ino, n_rec))
        o = self.table_offsets[idx] + 16 * node_id
        mib, sync, mount = struct.unpack_from("<QII", self.base, o)
        mib = self.overrides.get((ino, node_id), mib)
        return mib, sync, mount

    def metablock_to_block(self, mb):
        total = 0
        for begin, length in self.meta_extents:
            if mb < total + length:
                return begin + (mb - total)
            total += length
        raise VdfsError("metablock %d outside metadata extents" % mb)

    # ---- b-tree access
    def get_bnode(self, ino, node_id):
        mib, sync, mount = self.table_record(ino, node_id)
        blk = self.metablock_to_block(mib)
        data = self.read_at(blk * self.block_size, self.bnode_size)
        if data[:2] not in (b"eH", b"Nd"):
            raise VdfsError("tree %d node %d: bad bnode magic %r at block %d"
                            % (ino, node_id, data[:4], blk))
        return data

    @staticmethod
    def bnode_desc(data):
        magic = data[:4]
        free, recs = struct.unpack_from("<HH", data, 12)
        node_id, prev_id, next_id, ntype = struct.unpack_from("<IIII", data, 16)
        return magic, recs, node_id, prev_id, next_id, ntype

    def records_in_node(self, data):
        magic, recs, node_id, prev_id, next_id, ntype = self.bnode_desc(data)
        bs = self.bnode_size
        for i in range(recs):
            off, = struct.unpack_from("<I", data, bs - 4 - 4 * (i + 1))
            if off == 0 or off >= bs:
                self.warn("bad record offset %d in node %d" % (off, node_id))
                continue
            key_len, rec_len = struct.unpack_from("<HH", data, off + 4)
            yield off, key_len, rec_len

    def tree_leaves(self, ino):
        """Yield leaf bnodes of tree `ino` in key order."""
        head = self.get_bnode(ino, 0)
        root, = struct.unpack_from("<I", head, 12)
        height, = struct.unpack_from("<H", head, 16)
        node = root
        data = self.get_bnode(ino, node)
        depth = 0
        while self.bnode_desc(data)[5] == NODE_INDEX:
            recs = list(self.records_in_node(data))
            if not recs:
                raise VdfsError("empty index node %d" % node)
            off, key_len, _ = recs[0]
            node, = struct.unpack_from("<I", data, off + key_len)
            data = self.get_bnode(ino, node)
            depth += 1
            if depth > 32:
                raise VdfsError("b-tree too deep")
        seen = set()
        while True:
            nid = self.bnode_desc(data)[2]
            if nid in seen:
                raise VdfsError("loop in leaf chain")
            seen.add(nid)
            yield data
            nxt = self.bnode_desc(data)[4]
            if nxt == 0:
                return
            data = self.get_bnode(ino, nxt)

    # ---- catalog
    def load_catalog(self):
        self.by_id = {}        # object_id -> inode Entry (folder or file)
        self.children = {}     # parent_id -> [(name, Entry or ('hlink', object_id))]
        hlinks = []
        n = 0
        for leaf in self.tree_leaves(INO_CAT):
            for off, key_len, rec_len in self.records_in_node(leaf):
                parent_id, object_id, rtype, name_len = struct.unpack_from("<QQBB", leaf, off + 8)
                name = leaf[off + 26: off + 26 + name_len].decode("utf-8", "replace")
                val = off + key_len
                if rtype == REC_FOLDER or rtype == REC_FILE:
                    e = self._parse_inode(leaf, val, rtype)
                    e.object_id, e.parent_id, e.name = object_id, parent_id, name
                    if rtype == REC_FILE and parent_id == object_id and name_len == 0:
                        self.by_id[object_id] = e       # real hard-linked inode
                    else:
                        self.by_id.setdefault(object_id, e)
                        self.children.setdefault(parent_id, []).append(e)
                elif rtype == REC_HLINK:
                    hlinks.append((parent_id, object_id, name))
                n += 1
        for parent_id, object_id, name in hlinks:
            real = self.by_id.get(object_id)
            if real is None:
                self.warn("hard link %s -> missing inode %d" % (name, object_id))
                continue
            link = Entry()
            for s in Entry.__slots__:
                setattr(link, s, getattr(real, s, None))
            link.parent_id, link.name = parent_id, name
            self.children.setdefault(parent_id, []).append(link)
        self.catalog_records = n
        return n

    def _parse_inode(self, data, v, rtype):
        e = Entry()
        e.rtype = rtype
        flags, gen, total, links, orphan = struct.unpack_from("<IIQQQ", data, v)
        mode, pad, uid, gid = struct.unpack_from("<HHII", data, v + 32)
        mt_s, mt_hi, mt_ns = struct.unpack_from("<III", data, v + 44 + 12)
        e.flags, e.links, e.items = flags, links, total
        e.mode, e.uid, e.gid = mode, uid, gid
        e.mtime = mt_s + (mt_hi << 32)
        e.size = 0
        e.fork = None
        if rtype == REC_FILE:
            fv = v + 80
            size, tblocks = struct.unpack_from("<QQ", data, fv)
            e.size = size
            e.fork = bytes(data[fv:fv + 232])
        return e

    # ---- extent overflow tree
    def load_exttree(self):
        self.ext_over = {}
        try:
            for leaf in self.tree_leaves(INO_EXT):
                for off, key_len, rec_len in self.records_in_node(leaf):
                    obj, iblock = struct.unpack_from("<QQ", leaf, off + 8)
                    begin, length = struct.unpack_from("<QQ", leaf, off + key_len)
                    self.ext_over.setdefault(obj, []).append((iblock, begin, length))
        except VdfsError as ex:
            self.warn("extent tree unreadable: %s" % ex)

    # ---- file data
    def file_extents(self, e):
        out = []
        fork = e.fork
        for i in range(9):
            begin, length, iblock = struct.unpack_from("<QQQ", fork, 16 + 24 * i)
            if length:
                out.append((iblock, begin, length))
        if bit(e.flags, F_HAS_BLOCKS_IN_EXTTREE) or e.object_id in getattr(self, "ext_over", {}):
            out += self.ext_over.get(e.object_id, [])
        out.sort()
        return out

    def read_blob(self, e, size):
        bs = self.block_size
        buf = bytearray()
        for iblock, begin, length in self.file_extents(e):
            want = iblock * bs
            if want > len(buf):
                buf += b"\0" * (want - len(buf))
            if len(buf) >= size:
                break
            n = min(length * bs, max(0, size - want))
            if n <= 0:
                continue
            buf += self.read_at(begin * bs, n)
        if len(buf) < size:
            buf += b"\0" * (size - len(buf))
        return bytes(buf[:size])

    def read_file(self, e):
        """Return file contents as bytes."""
        if e.fork is None:
            return b""
        if bit(e.flags, F_ENCRYPTED):
            raise VdfsError("file is encrypted (key needed)")
        if bit(e.flags, F_INLINE):
            return e.fork[16:16 + e.size]
        if bit(e.flags, F_COMP_INLINE):
            ctype = e.fork[16:19].decode("ascii", "replace")
            csz = e.fork[19]
            return decompress_chunk(ctype, e.fork[20:20 + csz], e.size)
        if e.size == 0:
            return b""
        blob = self.read_blob(e, e.size)
        if bit(e.flags, F_COMPRESSED):
            return self.unpack_compressed(blob)
        return blob

    def unpack_compressed(self, blob):
        n = len(blob)
        if n < 40:
            raise VdfsError("compressed blob too small")
        d = blob[-40:]
        magic = d[8:12]
        ext_n, layout = struct.unpack_from("<HH", d, 12)
        unpacked, crc, log_chunk = struct.unpack_from("<QII", d, 16)
        kind = magic[1:4].decode("ascii", "replace")
        if kind not in ("Zip", "Gzp", "Lzo", "Zst"):
            raise VdfsError("bad compressed-file descriptor magic %r" % magic)
        if layout == 5:
            descr_size, sign_type = 32, 1
        else:
            descr_size, sign_type = 40, d[7]
        sign_len = {0: 0, 1: 128, 2: 256}.get(sign_type, 0)
        hash_len = {ord("I"): 16, ord("H"): 20, ord("h"): 32}.get(magic[0], 0)
        first_ext = descr_size + ext_n * 16
        if hash_len:
            first_ext += hash_len * (ext_n + 1) + sign_len
        table_pos = n - first_ext
        if table_pos < 0:
            raise VdfsError("compressed descriptor inconsistent")
        chunk = 1 << log_chunk
        out = bytearray()
        for i in range(ext_n):
            flags, ln, start = struct.unpack_from("<2xHIQ", blob, table_pos + 16 * i)[0:3]
            raw = blob[start:start + ln]
            if len(raw) != ln:
                raise VdfsError("chunk %d outside blob" % i)
            if flags & 2:
                raise VdfsError("chunk is encrypted (key needed)")
            if flags & 1:
                out += raw
            else:
                out += decompress_chunk(kind, raw, chunk)
        return bytes(out[:unpacked])

    # ---- tree walking
    def walk(self, start_id=None):
        """Yield (path, Entry) depth-first (pre-order, sorted by name) from root."""
        if start_id is None:
            start_id = 1
        stack = [iter(("", sorted(self.children.get(start_id, []), key=lambda x: x.name))[1:] and
                      [("", k) for k in sorted(self.children.get(start_id, []),
                                               key=lambda x: x.name)])]
        seen = {start_id}
        while stack:
            try:
                base, k = next(stack[-1])
            except StopIteration:
                stack.pop()
                continue
            path = base + "/" + k.name
            yield path, k
            if k.rtype == REC_FOLDER and k.object_id not in seen:
                seen.add(k.object_id)
                kids = sorted(self.children.get(k.object_id, []), key=lambda x: x.name)
                stack.append(iter([(path, c) for c in kids]))

    def lookup(self, path):
        parts = [p for p in path.split("/") if p]
        cur = 1
        entry = None
        for p in parts:
            entry = None
            for k in self.children.get(cur, []):
                if k.name == p:
                    entry = k
                    break
            if entry is None:
                raise VdfsError("path not found: %s" % path)
            cur = entry.object_id
        return cur, entry


# ---------------------------------------------------------------- CLI
def win_safe(name):
    bad = '<>:"\\|?*'
    out = "".join("_" if (c in bad or ord(c) < 32) else c for c in name)
    out = out.rstrip(" .") or "_"
    if out.upper().split(".")[0] in ("CON", "PRN", "AUX", "NUL", "COM1", "COM2", "COM3",
                                     "COM4", "LPT1", "LPT2", "LPT3"):
        out = "_" + out
    return out


def long_path(p):
    if os.name == "nt":
        p = os.path.abspath(p)
        if not p.startswith("\\\\?\\"):
            p = "\\\\?\\" + p
    return p


def fmt_mode(m):
    t = {stat_mod.S_IFDIR: "d", stat_mod.S_IFLNK: "l", stat_mod.S_IFREG: "-",
         stat_mod.S_IFCHR: "c", stat_mod.S_IFBLK: "b", stat_mod.S_IFIFO: "p",
         stat_mod.S_IFSOCK: "s"}.get(stat_mod.S_IFMT(m), "?")
    return t + stat_mod.filemode(m)[1:]


def main():
    ap = argparse.ArgumentParser(description="Extract files from a VDFS4 image")
    ap.add_argument("image")
    ap.add_argument("--info", action="store_true", help="print volume information")
    ap.add_argument("--list", action="store_true", help="list files")
    ap.add_argument("--extract", metavar="OUTDIR", help="extract files to OUTDIR")
    ap.add_argument("--path", default="/", help="only this directory/file (default /)")
    ap.add_argument("--verbose", "-v", action="store_true")
    ap.add_argument("--lenient", action="store_true",
                    help="zero-fill reads past end of image (for partial dumps)")
    a = ap.parse_args()
    try:
        sys.stdout.reconfigure(errors="replace")
        sys.stderr.reconfigure(errors="replace")
    except Exception:
        pass

    v = Vdfs(a.image, strict=not a.lenient)
    if a.info or not (a.list or a.extract):
        print("image          :", a.image, "(%d bytes)" % v.file_size)
        print("layout version :", v.layout_version, "  mkfs:", v.mkfs_version)
        print("volume name    :", v.volume_name)
        print("block / bnode  :", v.block_size, "/", v.bnode_size)
        print("blocks         :", v.max_blocks)
        print("files/folders  :", v.files_count, "/", v.folders_count, " inodes:", v.inode_count)
        print("hash/sign type :", v.hash_type, "/", v.sign_type, " encrypted flags:", v.enc_flags)
        print("meta extents   :", v.meta_extents)
        print("snapshot table : block", v.table_off // v.block_size,
              "crc ok" if v.base_crc_ok else "CRC MISMATCH",
              "| overrides:", len(v.overrides))
        if not (a.list or a.extract):
            return

    print("reading catalog ...", file=sys.stderr)
    cnt = v.load_catalog()
    v.load_exttree()
    print("catalog records: %d, inodes: %d" % (cnt, len(v.by_id)), file=sys.stderr)

    start_id, start_entry = v.lookup(a.path)
    if start_entry is not None and start_entry.rtype == REC_FILE:
        items = [(a.path, start_entry)]
    else:
        items = list(v.walk(start_id))
        base = a.path.rstrip("/")
        if base:
            items = [(base + p, e) for p, e in items]

    if a.list:
        for p, e in items:
            print("%s %5d %5d %10d  %s" % (fmt_mode(e.mode), e.uid, e.gid, e.size, p))

    if a.extract:
        out_root = a.extract
        os.makedirs(long_path(out_root), exist_ok=True)
        manifest = []
        safe_map = {}   # original path -> chosen on-disk path
        taken = set()   # on-disk paths already used (lower-cased on Windows)
        fold = (lambda x: x.lower()) if os.name == "nt" else (lambda x: x)

        def map_path(parts):
            orig = safe = ""
            for part in parts:
                orig += "/" + part
                if orig in safe_map:
                    safe = safe_map[orig]
                    continue
                cand, n = safe + "/" + part, 1
                while fold(cand) in taken:
                    n += 1
                    cand = safe + "/" + part + "~%d" % n
                taken.add(fold(cand))
                safe_map[orig] = cand
                safe = cand
            return safe

        ok = fail = skipped = 0
        total = len(items)
        for idx, (p, e) in enumerate(items):
            parts = [win_safe(x) if os.name == "nt" else x for x in p.split("/") if x]
            dest = os.path.join(out_root, *[q for q in map_path(parts).split("/") if q])
            fmtm = stat_mod.S_IFMT(e.mode)
            status = "ok"
            try:
                if e.rtype == REC_FOLDER and fmtm == stat_mod.S_IFDIR:
                    os.makedirs(long_path(dest), exist_ok=True)
                elif fmtm == stat_mod.S_IFLNK:
                    target = v.read_file(e).decode("utf-8", "replace")
                    os.makedirs(long_path(os.path.dirname(dest)), exist_ok=True)
                    made = False
                    try:
                        os.symlink(target, dest)
                        made = True
                    except (OSError, NotImplementedError):
                        pass
                    if not made:
                        with open(long_path(dest + ".symlink.txt"), "w", encoding="utf-8",
                                  errors="replace") as fh:
                            fh.write(target)
                    status = "symlink -> " + target
                elif fmtm == stat_mod.S_IFREG:
                    data = v.read_file(e)
                    os.makedirs(long_path(os.path.dirname(dest)), exist_ok=True)
                    with open(long_path(dest), "wb") as fh:
                        fh.write(data)
                    if e.mtime > 0:
                        try:
                            os.utime(long_path(dest), (e.mtime, e.mtime))
                        except OSError:
                            pass
                else:
                    status = "special file (not extracted)"
                    skipped += 1
                ok += 1
            except Exception as ex:   # keep going; report at the end
                status = "FAILED: %s" % ex
                fail += 1
                if a.verbose:
                    print("FAILED", p, ex, file=sys.stderr)
            manifest.append((p, oct(e.mode), e.uid, e.gid, e.size, status))
            if (idx + 1) % 500 == 0:
                print("  %d / %d" % (idx + 1, total), file=sys.stderr, flush=True)
        with open(os.path.join(out_root, "_vdfs_manifest.csv"), "w", newline="",
                  encoding="utf-8", errors="replace") as fh:
            w = csv.writer(fh)
            w.writerow(["path", "mode", "uid", "gid", "size", "status"])
            w.writerows(manifest)
        print("done: %d ok, %d failed, %d special/skipped" % (ok, fail, skipped))
        reasons = {}
        for row in manifest:
            if row[5].startswith("FAILED"):
                reasons[row[5]] = reasons.get(row[5], 0) + 1
        for r, c in sorted(reasons.items(), key=lambda x: -x[1])[:10]:
            print("  %5d x %s" % (c, r))
        print("manifest (modes/owners/symlinks): %s" %
              os.path.join(out_root, "_vdfs_manifest.csv"))

    if v.warnings:
        print("\nwarnings (%d):" % len(v.warnings), file=sys.stderr)
        for w in v.warnings[:20]:
            print("  -", w, file=sys.stderr)


if __name__ == "__main__":
    try:
        main()
    except VdfsError as ex:
        print("error:", ex, file=sys.stderr)
        sys.exit(2)
