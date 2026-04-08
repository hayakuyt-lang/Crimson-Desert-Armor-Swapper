"""
Hexe Marie Armor Swapper v2
============================
Auto-detects Crimson Desert, extracts iteminfo.pabgb, shows only armor items
organized by category (Chest / Gloves / Boots / Helm / Cloak) with clean names.

Requirements:
    pip install cryptography lz4

Usage:
    python armor_swapper.py
"""

import os
import sys
import json
import struct
import re
import threading
import platform
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional

import tkinter as tk
import tkinter.ttk as ttk
import tkinter.filedialog as filedialog
import tkinter.messagebox as messagebox

# ─── Dependency check ─────────────────────────────────────────────────────────
try:
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms
    HAS_CRYPTO = True
except ImportError:
    HAS_CRYPTO = False

try:
    import lz4.block
    HAS_LZ4 = True
except ImportError:
    HAS_LZ4 = False

# ─── Category detection ───────────────────────────────────────────────────────
CAT_ICONS = {
    "All": "⚔", "Chest": "🛡", "Gloves": "🧤",
    "Boots": "👢", "Helm": "⛑", "Cloak": "🧥",
    "Shoulder": "🔱", "Other": "✦",
}

# Armor slot endings for precise matching
ARMOR_ENDINGS = {
    "Gloves":  "Gloves",
    "Boots":   "Boots",
    "Helm":    "Helm",
    "Cloak":   "Cloak",
    "Armor":   "Chest",
}

def get_exact_type(name: str) -> str:
    """Returns exact armor slot for compatibility checking."""
    for ending, slot in ARMOR_ENDINGS.items():
        if name.endswith(ending):
            return slot
    # Fallback to keyword matching
    n = name.lower()
    if any(k in n for k in ['glove', 'hand_00']): return 'Gloves'
    if any(k in n for k in ['boot', 'foot_00']): return 'Boots'
    if any(k in n for k in ['helm', 'head_00']): return 'Helm'
    if any(k in n for k in ['cloak', 'cape']): return 'Cloak'
    if any(k in n for k in ['shoulder']): return 'Shoulder'
    return ""

def get_category(name: str) -> Optional[str]:
    n = name.lower()
    if any(k in n for k in ['glove', 'hand_00', '_hand_']): return 'Gloves'
    if any(k in n for k in ['boot', 'foot_00', '_foot_', 'shoe']): return 'Boots'
    if any(k in n for k in ['helm', 'head_00', '_head_', 'hat', 'hood', 'crown']): return 'Helm'
    if any(k in n for k in ['cloak', 'cape', 'mantle']): return 'Cloak'
    if any(k in n for k in ['shoulder', 'pauldron']): return 'Shoulder'
    if any(k in n for k in ['armor', 'platearmor', 'leatherarmor', 'mailarmor',
                              'robe', 'cuirass', 'breastplate', 'tunic', 'jacket']): return 'Chest'
    return None

def clean_name(name: str) -> str:
    # Split camelCase
    s = re.sub(r'([a-z])([A-Z])', r'\1 \2', name)
    # Replace underscores
    s = s.replace('_', ' ')
    # Remove duplicate spaces
    s = re.sub(r' +', ' ', s).strip()
    # Fix double "Armor Armor"
    s = re.sub(r'\bArmor\s+Armor\b', 'Armor', s)
    return s

# ─── CrimsonForge crypto ──────────────────────────────────────────────────────
HASH_INITVAL = 0x000C5EDE
IV_XOR       = 0x60616263
XOR_DELTAS   = [0x00000000, 0x0A0A0A0A, 0x0C0C0C0C, 0x06060606,
                0x0E0E0E0E, 0x0A0A0A0A, 0x06060606, 0x02020202]
MASK32 = 0xFFFFFFFF

def _rot(v, k): return ((v << k) | (v >> (32 - k))) & MASK32
def _add(a, b): return (a + b) & MASK32
def _sub(a, b): return (a - b) & MASK32

def hashlittle(data: bytes, initval: int = 0) -> int:
    length = len(data)
    a = b = c = _add(0xDEADBEEF + length, initval)
    off = 0
    while length > 12:
        a = _add(a, struct.unpack_from("<I", data, off)[0])
        b = _add(b, struct.unpack_from("<I", data, off+4)[0])
        c = _add(c, struct.unpack_from("<I", data, off+8)[0])
        a = _sub(a,c); a ^= _rot(c,4);  c = _add(c,b)
        b = _sub(b,a); b ^= _rot(a,6);  a = _add(a,c)
        c = _sub(c,b); c ^= _rot(b,8);  b = _add(b,a)
        a = _sub(a,c); a ^= _rot(c,16); c = _add(c,b)
        b = _sub(b,a); b ^= _rot(a,19); a = _add(a,c)
        c = _sub(c,b); c ^= _rot(b,4);  b = _add(b,a)
        off += 12; length -= 12
    tail = data[off:] + b"\x00"*12
    if length >= 12: c = _add(c, struct.unpack_from("<I",tail,8)[0])
    elif length >= 9: c = _add(c, struct.unpack_from("<I",tail,8)[0] & (MASK32>>(8*(12-length))))
    if length >= 8: b = _add(b, struct.unpack_from("<I",tail,4)[0])
    elif length >= 5: b = _add(b, struct.unpack_from("<I",tail,4)[0] & (MASK32>>(8*(8-length))))
    if length >= 4: a = _add(a, struct.unpack_from("<I",tail,0)[0])
    elif length >= 1: a = _add(a, struct.unpack_from("<I",tail,0)[0] & (MASK32>>(8*(4-length))))
    elif length == 0: return c
    c ^= b; c=_sub(c,_rot(b,14)); a ^= c; a=_sub(a,_rot(c,11))
    b ^= a; b=_sub(b,_rot(a,25)); c ^= b; c=_sub(c,_rot(b,16))
    a ^= c; a=_sub(a,_rot(c,4));  b ^= a; b=_sub(b,_rot(a,14))
    c ^= b; c=_sub(c,_rot(b,24))
    return c

def _derive_key_iv(filename: str):
    basename = os.path.basename(filename).lower()
    seed = hashlittle(basename.encode("utf-8"), HASH_INITVAL)
    iv = struct.pack("<I", seed) * 4
    key = b"".join(struct.pack("<I", (seed ^ IV_XOR) ^ d) for d in XOR_DELTAS)
    return key, iv

def decrypt_data(data: bytes, filename: str) -> bytes:
    key, iv = _derive_key_iv(filename)
    cipher = Cipher(algorithms.ChaCha20(key, iv), mode=None)
    return cipher.encryptor().update(data)

# ─── PAMT parser ──────────────────────────────────────────────────────────────
@dataclass
class FileEntry:
    path: str
    paz_file: str
    offset: int
    comp_size: int
    orig_size: int
    flags: int

    @property
    def compressed(self): return self.comp_size != self.orig_size
    @property
    def compression_type(self): return (self.flags >> 16) & 0x0F
    @property
    def encrypted(self):
        return os.path.splitext(self.path.lower())[1] in (
            ".xml",".paloc",".css",".html",".thtml",".pami",
            ".uianiminit",".spline2d",".spline",".mi",".txt")

def parse_pamt(pamt_path: str):
    paz_dir = os.path.dirname(pamt_path)
    pamt_stem = os.path.splitext(os.path.basename(pamt_path))[0]
    with open(pamt_path, "rb") as f: data = f.read()
    off = 4
    paz_count = struct.unpack_from("<I", data, off)[0]; off += 4
    off += 8
    for i in range(paz_count):
        off += 8
        if i < paz_count - 1: off += 4
    folder_size = struct.unpack_from("<I", data, off)[0]; off += 4
    folder_end = off + folder_size
    folder_prefix = ""
    while off < folder_end:
        parent = struct.unpack_from("<I", data, off)[0]
        slen = data[off+4]
        name = data[off+5:off+5+slen].decode("utf-8", errors="replace")
        if parent == 0xFFFFFFFF: folder_prefix = name
        off += 5 + slen
    node_size = struct.unpack_from("<I", data, off)[0]; off += 4
    node_start = off
    nodes = {}
    while off < node_start + node_size:
        rel = off - node_start
        parent = struct.unpack_from("<I", data, off)[0]
        slen = data[off+4]
        name = data[off+5:off+5+slen].decode("utf-8", errors="replace")
        nodes[rel] = (parent, name)
        off += 5 + slen
    def build_path(node_ref):
        parts = []; cur = node_ref; depth = 0
        while cur != 0xFFFFFFFF and depth < 64:
            if cur not in nodes: break
            p, n = nodes[cur]; parts.append(n); cur = p; depth += 1
        return "".join(reversed(parts))
    folder_count = struct.unpack_from("<I", data, off)[0]; off += 4
    off += 4; off += folder_count * 16
    entries = []
    while off + 20 <= len(data):
        node_ref, paz_offset, comp_size, orig_size, flags = struct.unpack_from("<IIIII", data, off)
        off += 20
        paz_index = flags & 0xFF
        node_path = build_path(node_ref)
        full_path = f"{folder_prefix}/{node_path}" if folder_prefix else node_path
        paz_num = int(pamt_stem) + paz_index
        paz_file = os.path.join(paz_dir, f"{paz_num}.paz")
        entries.append(FileEntry(path=full_path, paz_file=paz_file,
                                  offset=paz_offset, comp_size=comp_size,
                                  orig_size=orig_size, flags=flags))
    return entries

def read_entry(entry: FileEntry) -> bytes:
    read_size = entry.comp_size if entry.compressed else entry.orig_size
    with open(entry.paz_file, "rb") as f:
        f.seek(entry.offset); data = f.read(read_size)
    if entry.encrypted:
        data = decrypt_data(data, os.path.basename(entry.path))
    if entry.compressed and entry.compression_type == 2:
        data = lz4.block.decompress(data, uncompressed_size=entry.orig_size)
    return data

# ─── Steam auto-detection ─────────────────────────────────────────────────────
def _parse_vdf(vdf_path):
    try:
        with open(vdf_path, "r", encoding="utf-8") as f: content = f.read()
        return [p.replace("\\\\", os.sep).replace("\\", os.sep)
                for p in re.findall(r'"path"\s+"([^"]+)"', content)]
    except: return []

def auto_discover_game() -> Optional[str]:
    system = platform.system()
    roots = []
    if system == "Windows":
        default = "C:\\Program Files (x86)\\Steam"
        roots.append(os.path.join(default, "steamapps"))
        vdf = os.path.join(default, "steamapps", "libraryfolders.vdf")
        if os.path.isfile(vdf):
            roots.extend(os.path.join(p, "steamapps") for p in _parse_vdf(vdf))
        for env in ("ProgramFiles(x86)", "ProgramFiles"):
            base = os.environ.get(env, "")
            if base:
                cand = os.path.join(base, "Steam", "steamapps")
                if cand not in roots: roots.append(cand)
    elif system == "Darwin":
        sd = str(Path.home() / "Library" / "Application Support" / "Steam")
        vdf = os.path.join(sd, "steamapps", "libraryfolders.vdf")
        roots = [os.path.join(sd, "steamapps")]
        roots.extend(os.path.join(p, "steamapps") for p in _parse_vdf(vdf))
    else:
        for sd in [str(Path.home()/".steam"/"steam"),
                   str(Path.home()/".local"/"share"/"Steam")]:
            vdf = os.path.join(sd, "steamapps", "libraryfolders.vdf")
            if os.path.isfile(vdf):
                roots.append(os.path.join(sd, "steamapps"))
                roots.extend(os.path.join(p, "steamapps") for p in _parse_vdf(vdf))
                break

    for steamapps in roots:
        for name in ["Crimson Desert", "CrimsonDesert"]:
            game_root = os.path.join(steamapps, "common", name)
            if os.path.isdir(game_root):
                if os.path.isfile(os.path.join(game_root, "0008", "0.pamt")):
                    return game_root
    return None

# ─── iteminfo parser ──────────────────────────────────────────────────────────
@dataclass
class ArmorItem:
    id: int
    internal_name: str
    display_name: str
    category: str
    exact_type: str = ""
    hashes: list = field(default_factory=list)

FULL_MARKER = bytes([0x00,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x07,0x70,0x00,0x00,0x00])

def parse_iteminfo(data: bytes, loc_dict: dict = None) -> list[ArmorItem]:
    results = []; seen_ids = set(); idx = 0
    while True:
        pos = data.find(FULL_MARKER, idx)
        if pos == -1: break
        idx = pos + len(FULL_MARKER)
        name_start = pos
        while name_start > 0 and 0x21 <= data[name_start-1] <= 0x7E:
            name_start -= 1
            if pos - name_start > 150: break
        if pos - name_start < 3 or name_start < 8: continue
        try: name = data[name_start:pos].decode("ascii")
        except: continue
        if not re.match(r"^[A-Za-z][A-Za-z0-9_]*$", name): continue
        name_len = struct.unpack_from("<I", data, name_start-4)[0]
        item_id  = struct.unpack_from("<I", data, name_start-8)[0]
        if name_len not in (len(name), len(name)+1): continue
        if item_id < 100 or item_id > 100_000_000: continue
        if item_id in seen_ids: continue
        category = get_category(name)
        if category is None: continue
        seen_ids.add(item_id)
        # Get real display name from localization
        loc_id = extract_loc_id(data, pos)
        real_name = ''
        if loc_dict and loc_id:
            real_name = loc_dict.get(loc_id, '')
        # CrimsonForge algorithm: scan for 0x0E marker after item entry
        hashes = []
        search_start = pos + 14
        search_end = min(len(data), pos + 800)
        for scan in range(search_start, search_end - 15):
            if data[scan] != 0x0E: continue
            count1 = struct.unpack_from("<I", data, scan+3)[0]
            count2 = struct.unpack_from("<I", data, scan+7)[0]
            if not (0 < count1 <= 5 and 0 < count2 <= 5): continue
            for h_idx in range(count2):
                value = struct.unpack_from("<I", data, scan+11+h_idx*4)[0]
                if value != 0:
                    hashes.append({"offset": scan+11+h_idx*4, "value": value})
            if hashes: break
        if hashes:
            results.append(ArmorItem(
                id=item_id, internal_name=name,
                display_name=real_name if real_name else clean_name(name),
                category=category,
                exact_type=get_exact_type(name) or category,
                hashes=hashes))
    results.sort(key=lambda x: (x.category, x.display_name))
    return results

# ─── Localization parser ─────────────────────────────────────────────────────
def parse_localization(data: bytes) -> dict:
    """Parse localizationstring_eng into loc_id -> display_name dict."""
    loc_dict = {}
    pos = 0
    while pos + 8 < len(data):
        slen = struct.unpack_from('<I', data, pos)[0]
        if slen == 0 or slen > 50000 or pos + 4 + slen > len(data):
            pos += 1; continue
        s_bytes = data[pos+4:pos+4+slen]
        if 6 <= slen <= 20 and all(0x30 <= b <= 0x39 for b in s_bytes):
            loc_id = s_bytes.decode('ascii')
            text_pos = pos + 4 + slen
            if text_pos + 4 < len(data):
                text_len = struct.unpack_from('<I', data, text_pos)[0]
                if 0 < text_len < 50000 and text_pos + 4 + text_len <= len(data):
                    try:
                        text = data[text_pos+4:text_pos+4+text_len].decode('utf-8', errors='replace')
                        loc_dict[loc_id] = text
                        pos = text_pos + 4 + text_len
                        continue
                    except: pass
        pos += 1
    return loc_dict

def extract_loc_id(data: bytes, marker_pos: int) -> str:
    """Extract loc_id from item entry at marker position."""
    loc_off = marker_pos + 14 + 4
    if loc_off + 4 >= len(data): return ''
    loc_len = struct.unpack_from('<I', data, loc_off)[0]
    if 5 < loc_len < 25 and loc_off + 4 + loc_len <= len(data):
        loc_bytes = data[loc_off+4:loc_off+4+loc_len]
        if all(0x30 <= b <= 0x39 for b in loc_bytes):
            return loc_bytes.decode('ascii')
    return ''

# ─── Patch builder ────────────────────────────────────────────────────────────
def to_le_hex(val: int) -> str:
    return struct.pack("<I", val).hex().upper()

def build_patch(swaps: list) -> dict:
    changes = []
    for swap in swaps:
        src_h = swap["source"].hashes; tgt_h = swap["target"].hashes
        if not src_h or not tgt_h: continue
        n = len(src_h)
        if n <= 2:   positions = [0]
        elif n <= 5: positions = [0, 2]
        else:        positions = [p for p in [0, 2, 5, 6] if p < n]
        for pos in positions:
            if pos >= len(tgt_h): continue
            src = src_h[pos]; tgt = tgt_h[pos]
            if src["value"] == tgt["value"]: continue
            changes.append({
                "offset": src["offset"],
                "label": f"{swap['source'].internal_name} -> {swap['target'].internal_name}",
                "original": to_le_hex(src["value"]),
                "patched":  to_le_hex(tgt["value"]),
            })
    return {
        "name": "Armor Visual Swap",
        "version": "1.0",
        "description": " | ".join(
            f"{s['source'].display_name} -> {s['target'].display_name}" for s in swaps),
        "author": "Generated by Hexe Marie Armor Swapper v2",
        "patches": [{"game_file": "gamedata/iteminfo.pabgb", "changes": changes}]
    }

# ─── Colors ───────────────────────────────────────────────────────────────────
C = {
    "bg":         "#0d0b09",
    "bg2":        "#161209",
    "bg3":        "#1e1812",
    "bg4":        "#251d14",
    "border":     "#2e2416",
    "gold":       "#c9a84c",
    "gold_light": "#f0d080",
    "gold_dark":  "#7a5c1e",
    "text":       "#e8dcc8",
    "text_dim":   "#7a6a50",
    "green":      "#4caf78",
    "red":        "#f08080",
}

# ─── App ──────────────────────────────────────────────────────────────────────
class ArmorSwapperApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Hexe Marie — Armor Swapper")
        self.root.geometry("1280x900")
        self.root.configure(bg=C["bg"])
        self.root.minsize(1100, 750)

        self.all_items:       list[ArmorItem] = []
        self.source_items:    list[ArmorItem] = []
        self.target_items:    list[ArmorItem] = []
        self.selected_source: Optional[ArmorItem] = None
        self.selected_target: Optional[ArmorItem] = None
        self.swaps:           list[dict] = []
        self.game_path:       str = ""
        self.active_cat:      str = "All"

        self._setup_styles()
        self._build_ui()
        self._auto_detect()

    def _setup_styles(self):
        s = ttk.Style(); s.theme_use("clam")
        s.configure("G.Treeview",
            background=C["bg2"], foreground=C["text"],
            fieldbackground=C["bg2"], borderwidth=0,
            font=("Segoe UI", 10), rowheight=30)
        s.configure("G.Treeview.Heading",
            background=C["bg3"], foreground=C["gold"],
            font=("Segoe UI", 9, "bold"), borderwidth=0, relief="flat")
        s.map("G.Treeview",
            background=[("selected", C["gold_dark"])],
            foreground=[("selected", C["gold_light"])])
        s.configure("G.Vertical.TScrollbar",
            background=C["bg3"], troughcolor=C["bg"],
            borderwidth=0, arrowcolor=C["gold_dark"])
        s.configure("G.Horizontal.TProgressbar",
            background=C["gold"], troughcolor=C["bg3"],
            borderwidth=0, thickness=4)

    def _build_ui(self):
        # Header
        hdr = tk.Frame(self.root, bg=C["bg"], pady=12)
        hdr.pack(fill="x")
        tk.Label(hdr, text="✦  HEXE MARIE  ✦", bg=C["bg"],
                 fg=C["gold_dark"], font=("Georgia", 8)).pack()
        tk.Label(hdr, text="Armor Swapper", bg=C["bg"],
                 fg=C["gold_light"], font=("Georgia", 22, "bold")).pack()
        tk.Label(hdr, text="Make any armor look like any other — stats stay unchanged",
                 bg=C["bg"], fg=C["text_dim"],
                 font=("Segoe UI", 9, "italic")).pack(pady=2)
        tk.Frame(self.root, bg=C["gold_dark"], height=1).pack(fill="x")

        # Body
        body = tk.Frame(self.root, bg=C["bg"])
        body.pack(fill="both", expand=True, padx=14, pady=12)

        # Left panel
        left = tk.Frame(body, bg=C["bg"], width=430)
        left.pack(side="left", fill="y", padx=(0,12))
        left.pack_propagate(False)
        self._build_left(left)

        # Right panel
        right = tk.Frame(body, bg=C["bg"])
        right.pack(side="left", fill="both", expand=True)
        self._build_right(right)

    def _build_left(self, parent):
        # Make left panel scrollable
        canvas = tk.Canvas(parent, bg=C["bg"], highlightthickness=0)
        scrollbar = tk.Scrollbar(parent, orient="vertical", command=canvas.yview)
        canvas.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        p = tk.Frame(canvas, bg=C["bg"])
        canvas_window = canvas.create_window((0,0), window=p, anchor="nw")
        def on_configure(e):
            canvas.configure(scrollregion=canvas.bbox("all"))
            canvas.itemconfig(canvas_window, width=canvas.winfo_width())
        p.bind("<Configure>", on_configure)
        canvas.bind("<Configure>", lambda e: canvas.itemconfig(canvas_window, width=e.width))
        # Mousewheel scrolling
        def on_mousewheel(e):
            canvas.yview_scroll(int(-1*(e.delta/120)), "units")
        canvas.bind_all("<MouseWheel>", on_mousewheel)

        # Game path
        gf = self._card(p, "Game Folder")
        self.path_var = tk.StringVar(value="Detecting...")
        tk.Label(gf, textvariable=self.path_var, bg=C["bg2"], fg=C["gold"],
                 font=("Courier New", 8), wraplength=380,
                 justify="left", anchor="w").pack(fill="x", pady=(0,6))
        row = tk.Frame(gf, bg=C["bg2"]); row.pack(fill="x", pady=(0,4))
        self._btn(row, "Browse...",        self._browse,       small=True).pack(side="left")
        self._btn(row, "⬇  Extract & Load", self._load, gold=True, small=True).pack(side="left", padx=(8,0))
        self.load_lbl = tk.Label(gf, text="", bg=C["bg2"], fg=C["text_dim"],
                                  font=("Segoe UI", 8), wraplength=380,
                                  justify="left", anchor="w")
        self.load_lbl.pack(fill="x")
        self.pbar = ttk.Progressbar(gf, style="G.Horizontal.TProgressbar",
                                     mode="determinate")

        # Category filter
        cf = self._card(p, "Filter by Category")
        cats = list(CAT_ICONS.keys())
        self.cat_btns = {}
        row1 = tk.Frame(cf, bg=C["bg2"]); row1.pack(fill="x", pady=(0,4))
        row2 = tk.Frame(cf, bg=C["bg2"]); row2.pack(fill="x")
        for i, cat in enumerate(cats):
            row = row1 if i < 4 else row2
            b = tk.Button(row, text=f"{CAT_ICONS[cat]} {cat}",
                           command=lambda c=cat: self._select_cat(c),
                           bg=C["bg3"], fg=C["text_dim"],
                           activebackground=C["gold_dark"],
                           activeforeground=C["gold_light"],
                           relief="flat", bd=0, cursor="hand2",
                           font=("Segoe UI", 8), padx=8, pady=5)
            b.pack(side="left", padx=(0,4))
            self.cat_btns[cat] = b

        # Source
        sf = self._card(p, "Source  —  Armor you EQUIP  (for stats)")
        self.src_var = tk.StringVar()
        self.src_var.trace("w", lambda *a: self._refresh("src"))
        self._entry(sf, self.src_var, "Search by name...")
        self.src_lb = self._lb(sf, self._pick_src, 6)

        # Target
        tf = self._card(p, "Target  —  How you want it to LOOK")
        self.tgt_var = tk.StringVar()
        self.tgt_var.trace("w", lambda *a: self._refresh("tgt"))
        self._entry(tf, self.tgt_var, "Search by name...")
        self.tgt_lb = self._lb(tf, self._pick_tgt, 6)

        # Preview + Add
        af = self._card(p, "Add Swap")
        prev = tk.Frame(af, bg=C["bg3"], padx=10, pady=8)
        prev.pack(fill="x", pady=(0,8))
        self.p_src = tk.Label(prev, text="Equip:  —", bg=C["bg3"],
                               fg=C["text_dim"], font=("Segoe UI", 9), anchor="w")
        self.p_src.pack(fill="x")
        tk.Label(prev, text="   ↓  will visually appear as",
                 bg=C["bg3"], fg=C["gold_dark"],
                 font=("Segoe UI", 8, "italic"), anchor="w").pack(fill="x")
        self.p_tgt = tk.Label(prev, text="Look:   —", bg=C["bg3"],
                               fg=C["text_dim"], font=("Segoe UI", 9), anchor="w")
        self.p_tgt.pack(fill="x")
        self.add_btn = self._btn(af, "  +  Add This Swap", self._add, gold=True)
        self.add_btn.pack(fill="x")
        self.add_btn.configure(state="disabled")

        # Now safe to set active category since src_var and tgt_var exist
        self._select_cat("All")

    def _build_right(self, p):
        # Swap list
        sf = self._card(p, "Configured Swaps")
        sf.pack(fill="both", expand=True)
        cols = ("cat", "source", "arr", "target")
        self.tree = ttk.Treeview(sf, columns=cols, show="headings",
                                  style="G.Treeview", height=15)
        self.tree.heading("cat",    text="Type")
        self.tree.heading("source", text="Armor you EQUIP")
        self.tree.heading("arr",    text="→")
        self.tree.heading("target", text="Visual APPEARANCE")
        self.tree.column("cat",    width=90,  anchor="center")
        self.tree.column("source", width=290)
        self.tree.column("arr",    width=30,  anchor="center")
        self.tree.column("target", width=290)
        sb = ttk.Scrollbar(sf, orient="vertical",
                            style="G.Vertical.TScrollbar",
                            command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")

        # Actions
        act = tk.Frame(p, bg=C["bg"], pady=6); act.pack(fill="x")
        self._btn(act, "Remove Selected", self._remove, small=True).pack(side="left")
        self._btn(act, "Clear All",       self._clear,  small=True).pack(side="left", padx=(8,0))

        # Generate
        gf = self._card(p, "Generate Patch")
        gf.pack(fill="x", pady=(8,0))
        self.gen_lbl = tk.Label(gf,
            text="Add swaps above, then download the JSON patch file.",
            bg=C["bg2"], fg=C["text_dim"], font=("Segoe UI", 9),
            wraplength=500, justify="left", anchor="w")
        self.gen_lbl.pack(fill="x", pady=(0,8))
        br = tk.Frame(gf, bg=C["bg2"]); br.pack(fill="x")
        self._btn(br, "⬇  Download JSON Patch", self._download, gold=True).pack(side="left")
        self._btn(br, "Copy to Clipboard",       self._copy,   small=True).pack(side="left", padx=(10,0))

        # How to use
        hf = self._card(p, "How To Use")
        hf.pack(fill="x", pady=(8,0))
        for step in [
            "1.  Click 'Extract & Load' — auto-finds your game on Steam",
            "2.  Pick a category tab (Chest / Gloves / Boots / Helm / Cloak)",
            "3.  Source = the armor you EQUIP for stats",
            "4.  Target = the armor you want it to LOOK like",
            "5.  Click '+ Add This Swap', repeat for each armor piece",
            "6.  Download patch → drop in CD JSON Mod Manager → Apply",
        ]:
            tk.Label(hf, text=step, bg=C["bg2"], fg=C["text_dim"],
                     font=("Segoe UI", 8), anchor="w").pack(fill="x", pady=1)

    # ── Helpers ───────────────────────────────────────────────────────────────
    def _card(self, parent, title):
        outer = tk.Frame(parent, bg=C["bg"])
        outer.pack(fill="x", pady=(0,8))
        tk.Label(outer, text=title.upper(), bg=C["bg"],
                 fg=C["gold_dark"], font=("Segoe UI", 7, "bold"),
                 pady=2).pack(anchor="w")
        inner = tk.Frame(outer, bg=C["bg2"],
                          highlightthickness=1,
                          highlightbackground=C["border"],
                          padx=10, pady=8)
        inner.pack(fill="both", expand=True)
        return inner

    def _btn(self, parent, text, cmd, gold=False, small=False):
        return tk.Button(parent, text=text, command=cmd,
                          bg=C["gold_dark"] if gold else C["bg3"],
                          fg=C["gold_light"] if gold else C["text_dim"],
                          activebackground=C["gold"],
                          activeforeground=C["bg"],
                          relief="flat", bd=0, cursor="hand2",
                          font=("Segoe UI", 9 if small else 10),
                          padx=14, pady=6)

    def _entry(self, parent, var, placeholder):
        # Use separate internal var so placeholder doesnt pollute search
        e = tk.Entry(parent,
                      bg=C["bg3"], fg=C["text_dim"],
                      insertbackground=C["gold"],
                      relief="flat", bd=0, font=("Segoe UI", 9),
                      highlightthickness=1,
                      highlightbackground=C["border"])
        e.pack(fill="x", pady=(0,6), ipady=5)
        e.insert(0, placeholder)
        def fi(ev):
            if e.get() == placeholder:
                e.delete(0, "end")
                e.config(fg=C["text"])
                var.set("")
        def fo(ev):
            if not e.get():
                e.insert(0, placeholder)
                e.config(fg=C["text_dim"])
                var.set("")
        def on_key(ev):
            var.set(e.get())
        e.bind("<FocusIn>", fi)
        e.bind("<FocusOut>", fo)
        e.bind("<KeyRelease>", on_key)
        return e

    def _lb(self, parent, cmd, height):
        frame = tk.Frame(parent, bg=C["bg3"],
                          highlightthickness=1,
                          highlightbackground=C["border"])
        frame.pack(fill="both", expand=True)
        lb = tk.Listbox(frame, bg=C["bg3"], fg=C["text"],
                         selectbackground=C["gold_dark"],
                         selectforeground=C["gold_light"],
                         relief="flat", bd=0, font=("Segoe UI", 9),
                         activestyle="none", height=height)
        sb = tk.Scrollbar(frame, orient="vertical", command=lb.yview)
        lb.configure(yscrollcommand=sb.set)
        lb.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        lb.bind("<<ListboxSelect>>", cmd)
        return lb

    # ── Logic ─────────────────────────────────────────────────────────────────
    def _auto_detect(self):
        def run():
            path = auto_discover_game()
            if path:
                self.game_path = path
                short = ("..." + path[-45:]) if len(path) > 48 else path
                self.root.after(0, lambda: self.path_var.set(short))
                self.root.after(0, lambda: self.load_lbl.config(
                    text="✓ Game found! Click 'Extract & Load' to continue.",
                    fg=C["green"]))
            else:
                self.root.after(0, lambda: self.path_var.set("Not found"))
                self.root.after(0, lambda: self.load_lbl.config(
                    text="Could not auto-detect. Use Browse.",
                    fg=C["text_dim"]))
        threading.Thread(target=run, daemon=True).start()

    def _browse(self):
        path = filedialog.askdirectory(title="Select Crimson Desert folder")
        if path:
            self.game_path = path
            self.path_var.set(path)
            self.load_lbl.config(text="Ready. Click 'Extract & Load'.",
                                  fg=C["text_dim"])

    def _load(self):
        if not self.game_path:
            messagebox.showerror("Error", "No game folder set.")
            return
        self.load_lbl.config(text="Locating iteminfo.pabgb...", fg=C["gold"])
        self.pbar.pack(fill="x", pady=(6,0))
        self.pbar["value"] = 0

        def run():
            try:
                self.root.after(0, lambda: self._p(10))
                pamt_path = os.path.join(self.game_path, "0008", "0.pamt")
                if not os.path.isfile(pamt_path):
                    self.root.after(0, lambda: self.load_lbl.config(
                        text="Cannot find 0008/0.pamt — check game folder.",
                        fg=C["red"]))
                    return
                entries = parse_pamt(pamt_path)
                self.root.after(0, lambda: self._p(30))
                item_entry = next((e for e in entries
                                    if "iteminfo.pabgb" in e.path.lower()), None)
                if not item_entry:
                    self.root.after(0, lambda: self.load_lbl.config(
                        text="iteminfo.pabgb not found in 0008.",
                        fg=C["red"]))
                    return
                self.root.after(0, lambda: self.load_lbl.config(
                    text="Loading localization...", fg=C["gold"]))
                self.root.after(0, lambda: self._p(40))
                # Load localization from 0020
                loc_dict = {}
                try:
                    pamt_0020 = os.path.join(self.game_path, "0020", "0.pamt")
                    if os.path.isfile(pamt_0020):
                        entries_0020 = parse_pamt(pamt_0020)
                        loc_entry = next((e for e in entries_0020
                            if "localizationstring_eng" in e.path.lower()), None)
                        if loc_entry:
                            loc_data = read_entry(loc_entry)
                            loc_dict = parse_localization(loc_data)
                except Exception as le:
                    pass  # Localization optional - fall back to internal names
                self.root.after(0, lambda: self.load_lbl.config(
                    text="Decrypting & decompressing iteminfo...", fg=C["gold"]))
                self.root.after(0, lambda: self._p(55))
                data = read_entry(item_entry)
                self.root.after(0, lambda: self.load_lbl.config(
                    text="Parsing armor items...", fg=C["gold"]))
                self.root.after(0, lambda: self._p(75))
                items = parse_iteminfo(data, loc_dict)
                self.all_items = items
                self.root.after(0, lambda: self._p(100))
                self.root.after(0, self._on_loaded)
            except Exception as ex:
                import traceback; traceback.print_exc()
                self.root.after(0, lambda: self.load_lbl.config(
                    text=f"Error: {ex}", fg=C["red"]))

        threading.Thread(target=run, daemon=True).start()

    def _p(self, v): self.pbar["value"] = v

    def _on_loaded(self):
        self.pbar.pack_forget()
        cats = {}
        for item in self.all_items:
            cats[item.category] = cats.get(item.category, 0) + 1
        summary = "  ".join(f"{k}:{v}" for k,v in sorted(cats.items()))
        self.load_lbl.config(
            text=f"✓ {len(self.all_items):,} armor items loaded  |  {summary}",
            fg=C["green"])
        self._refresh("src")
        self._refresh("tgt")

    def _select_cat(self, cat):
        self.active_cat = cat
        for c, b in self.cat_btns.items():
            b.configure(
                bg=C["gold_dark"] if c == cat else C["bg3"],
                fg=C["gold_light"] if c == cat else C["text_dim"])
        self._refresh("src")
        self._refresh("tgt")

    def _filtered(self, query, target_side=False):
        items = self.all_items
        if self.active_cat != "All":
            items = [i for i in items if i.category == self.active_cat]
        if target_side and self.selected_source:
            items = [i for i in items if i.exact_type == self.selected_source.exact_type]
        q = query.strip().lower()
        if q and q != "search by name...".lower():
            items = [i for i in items
                     if q in i.display_name.lower() or
                        q in i.internal_name.lower()]
        return items[:300]

    def _refresh(self, side):
        if side == "src":
            q = self.src_var.get()
            self.source_items = self._filtered(q)
            self._fill(self.src_lb, self.source_items)
            # Reselect if still in list
            if self.selected_source:
                for i, item in enumerate(self.source_items):
                    if item.id == self.selected_source.id:
                        self.src_lb.selection_set(i)
                        self.src_lb.see(i)
                        break
        else:
            q = self.tgt_var.get()
            self.target_items = self._filtered(q, target_side=True)
            self._fill(self.tgt_lb, self.target_items)
            # Reselect if still in list
            if self.selected_target:
                for i, item in enumerate(self.target_items):
                    if item.id == self.selected_target.id:
                        self.tgt_lb.selection_set(i)
                        self.tgt_lb.see(i)
                        break

    def _fill(self, lb, items):
        lb.delete(0, "end")
        if not items:
            lb.insert("end", "  No items found"); return
        for item in items:
            lb.insert("end", f"  {item.display_name}")

    def _pick_src(self, event):
        sel = self.src_lb.curselection()
        if not sel: return
        idx = sel[0]
        if idx < len(self.source_items):
            self.selected_source = self.source_items[idx]
            self.p_src.config(
                text=f"Equip:  {self.selected_source.display_name}",
                fg=C["text"])
            self._refresh("tgt")
        self._check_add()

    def _pick_tgt(self, event):
        sel = self.tgt_lb.curselection()
        if not sel: return
        idx = sel[0]
        if idx < len(self.target_items):
            self.selected_target = self.target_items[idx]
            self.p_tgt.config(
                text=f"Look:   {self.selected_target.display_name}",
                fg=C["gold"])
        self._check_add()

    def _check_add(self):
        ok = bool(self.selected_source and self.selected_target)
        self.add_btn.configure(
            state="normal" if ok else "disabled",
            bg=C["gold_dark"] if ok else C["bg3"],
            fg=C["gold_light"] if ok else C["text_dim"])

    def _add(self):
        if not self.selected_source or not self.selected_target: return
        if self.selected_source.id == self.selected_target.id:
            messagebox.showwarning("Same item",
                "Source and target are the same armor piece!"); return
        if self.selected_source.exact_type != self.selected_target.exact_type:
            messagebox.showerror("Incompatible Slots",
                "Cannot swap! Source is " + self.selected_source.exact_type + " but target is " + self.selected_target.exact_type + ". You can only swap the same armor slot!"); return
        if any(s["source"].id == self.selected_source.id for s in self.swaps):
            messagebox.showwarning("Duplicate",
                "This armor already has a swap configured."); return
        self.swaps.append({"source": self.selected_source,
                            "target": self.selected_target})
        self.tree.insert("", "end", values=(
            self.selected_source.category,
            self.selected_source.display_name,
            "→",
            self.selected_target.display_name,
        ))
        self.gen_lbl.config(
            text=f"✓ {len(self.swaps)} swap(s) configured. Download when ready!",
            fg=C["green"])

    def _remove(self):
        for item in self.swap_tree.selection() if hasattr(self,'swap_tree') else self.tree.selection():
            idx = self.tree.index(item)
            if idx < len(self.swaps): self.swaps.pop(idx)
            self.tree.delete(item)

    def _clear(self):
        self.swaps.clear()
        for item in self.tree.get_children(): self.tree.delete(item)
        self.gen_lbl.config(text="All swaps cleared.", fg=C["text_dim"])

    def _download(self):
        if not self.swaps:
            messagebox.showwarning("No swaps", "Add at least one swap first.")
            return
        patch = build_patch(self.swaps)
        if not patch["patches"][0]["changes"]:
            messagebox.showerror("Error",
                "No valid hash changes found. Try different items.")
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json")],
            initialfile="armor_swap.json",
            title="Save JSON Patch")
        if path:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(patch, f, indent=2)
            n = len(patch["patches"][0]["changes"])
            self.gen_lbl.config(
                text=f"✓ Saved! {n} hash changes. Drop into CD JSON Mod Manager and Apply.",
                fg=C["green"])

    def _copy(self):
        if not self.swaps:
            messagebox.showwarning("No swaps", "Add at least one swap first.")
            return
        patch = build_patch(self.swaps)
        self.root.clipboard_clear()
        self.root.clipboard_append(json.dumps(patch, indent=2))
        self.gen_lbl.config(text="✓ Copied to clipboard!", fg=C["green"])


# ─── Entry ────────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    missing = []
    if not HAS_CRYPTO: missing.append("cryptography")
    if not HAS_LZ4:    missing.append("lz4")
    if missing:
        root = tk.Tk(); root.withdraw()
        messagebox.showerror("Missing Dependencies",
            f"Please install:\n\npip install {' '.join(missing)}")
        sys.exit(1)

    root = tk.Tk()
    ArmorSwapperApp(root)
    root.mainloop()
