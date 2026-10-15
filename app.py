# -*- coding: utf-8 -*-
"""
===============================================================================
 SURVEI TKP LAKA — Mobile GIS untuk Laporan Polisi (LP)
 Divisi Survei Klaim · Jasa Raharja
-------------------------------------------------------------------------------
 Alur kerja aplikasi:
   1. Upload banyak LP sekaligus: PDF, Word (.doc / .docx), RTF, atau CSV
      hasil olahan sebelumnya.
   2. Teks diekstrak (pdfplumber / pembaca Word bawaan), regex mengambil No. LP,
      waktu, blok "Tempat Kejadian", jalan, patokan, dusun, desa, kecamatan,
      kabupaten/kota.
   3. Geocoding berlapis via Nominatim (geopy). Setiap hasil WAJIB jatuh di
      dalam poligon kabupaten/kota yang tertulis di LP → titik tidak bisa
      "nyasar" ke kota lain. TIDAK ADA kabupaten default.
   4. Peta Folium + tile Google Maps + MarkerCluster, lingkaran radius dari
      GPS HP, dan daftar Card yang difilter sesuai radius.
   5. Tombol "Mulai Survei / Navigasi" membuka aplikasi Google Maps di Android.
   6. Data LP disimpan otomatis di HP (penyimpanan browser), tidak hilang saat
      aplikasi ditutup — tidak perlu upload ulang.
   7. Alarm TKP: saat Anda melintas ±500 m dari TKP, HP berbunyi, bergetar,
      dan menyebutkan TKP-nya (selama aplikasi terbuka & layar menyala).

 Jalankan lokal :  streamlit run app.py
 Secrets (opsional, di Streamlit Cloud → App settings → Secrets):
   APP_PASSWORD         = "kata-sandi-tim"         # kunci akses aplikasi
   NOMINATIM_USER_AGENT = "jr-survei-tkp/1.0 (email-anda@contoh.com)"
===============================================================================
"""

from __future__ import annotations

import email
import email.policy
import hashlib
import hmac
import html
import io
import json
import math
import os
import re
import secrets
import struct
import tempfile
import time
import urllib.parse
import xml.etree.ElementTree as ET
import zipfile
from datetime import datetime, timedelta, timezone
from html.parser import HTMLParser

import folium
import olefile
import pandas as pd
import pdfplumber
import streamlit as st
import streamlit.components.v1 as components
from folium.plugins import Fullscreen, LocateControl, MarkerCluster
from geopy.exc import GeopyError
from geopy.extra.rate_limiter import RateLimiter
from geopy.geocoders import Nominatim
from streamlit_folium import st_folium
from streamlit_geolocation import streamlit_geolocation

# =============================================================================
# 1. KONSTANTA & PENGATURAN
# =============================================================================
WIB = timezone(timedelta(hours=7))           # server Streamlit Cloud memakai UTC

TINGGI_PETA = 430                            # px — sisakan ruang untuk scroll di HP
RADIUS_MIN_KM, RADIUS_MAX_KM, RADIUS_DEFAULT_KM = 1, 15, 5
KARTU_PER_HALAMAN = 15                       # card per "halaman" agar HP tetap ringan
MAKS_HALAMAN_PDF = 6                         # info TKP selalu ada di halaman awal LP
DETIK_PER_PUTARAN = 20                       # proses batch per ±20 detik, lalu simpan ke HP
TOLERANSI_BATAS_KM = 0.5                     # toleransi untuk jalan tepat di garis batas
BATAS_INDONESIA = (-11.5, 6.5, 94.5, 141.5)  # lat_min, lat_max, lon_min, lon_max

# Tile Google Maps. Sengaja memakai HTTPS (bukan http://): Streamlit Cloud
# berjalan di HTTPS, dan browser HP memblokir gambar http:// (mixed content).
# {s} diganti Leaflet dengan mt0..mt3 supaya unduhan tile paralel & lebih cepat.
TILE_GOOGLE_JALAN = "https://mt{s}.google.com/vt/lyrs=m&hl=en&x={x}&y={y}&z={z}"
TILE_GOOGLE_HYBRID = "https://mt{s}.google.com/vt/lyrs=y&hl=en&x={x}&y={y}&z={z}"

STATUS_OK = "Berhasil"
STATUS_MANUAL = "Koordinat Manual"
STATUS_GAGAL = "Gagal - Cek Manual"

PRESISI_PATOKAN = "Patokan (pasar/SPBU/masjid, dll.)"
PRESISI_JALAN = "Jalan"
PRESISI_DUSUN = "Dusun"
PRESISI_DESA = "Desa/Kelurahan"
PRESISI_KEC = "Pusat kecamatan (perkiraan)"
PRESISI_KEC_LAMA = "Kecamatan (titik tengah)"     # label versi lama (CSV lama)
PRESISI_MANUAL = "Manual (surveyor)"
PRESISI_KASAR = {PRESISI_DUSUN, PRESISI_DESA, PRESISI_KEC, PRESISI_KEC_LAMA}

WARNA_MARKER = {           # warna folium.Icon per tingkat presisi
    PRESISI_PATOKAN: "red",
    PRESISI_JALAN: "red",
    PRESISI_DUSUN: "orange",
    PRESISI_DESA: "orange",
    PRESISI_KEC: "cadetblue",
    PRESISI_KEC_LAMA: "cadetblue",
    PRESISI_MANUAL: "purple",
}
EMOJI_PRESISI = {
    PRESISI_PATOKAN: "🔴",
    PRESISI_JALAN: "🔴",
    PRESISI_DUSUN: "🟠",
    PRESISI_DESA: "🟠",
    PRESISI_KEC: "🔵",
    PRESISI_KEC_LAMA: "🔵",
    PRESISI_MANUAL: "🟣",
}

# Validasi tambahan: hasil harus dekat kecamatan TKP (bukan sekadar di kabupaten).
TOLERANSI_KEC_KM = 3.0      # toleransi ke batas poligon kecamatan (data batas OSM sering kurang presisi)
RADIUS_KEC_KM = 12.0        # dipakai bila hanya titik pusat kecamatan yang diketahui
# Kata yang bukan bagian nama jalan: "Jalan Umum jurusan X - Y" → "Jalan X Y"
POLA_KATA_SAMPAH_JALAN = re.compile(r"\b(?:umum|jurusan)\b\.?", re.IGNORECASE)
# Jenis patokan yang biasa ada namanya di peta (OSM): "depan Pasar Tempel" → "Pasar Tempel"
KATA_POI = (
    r"pasar|masjid|musholl?a|mushola|langgar|gereja|pura|vihara|klenteng|sekolah|sdn?|smpn?|"
    r"sman?|smkn?|mts|mi|ma|pondok|ponpes|pesantren|spbu|puskesmas|rsud|rs|rumah\s+sakit|"
    r"klinik|apotek|kantor|balai|toko|warung|kios|swalayan|minimarket|alfamart|indomaret|"
    r"bank|pabrik|terminal|stasiun|"
    r"jembatan|makam|tpu|lapangan|stadion|taman|hotel|rumah\s+makan|bengkel|koramil|polsek|"
    r"kodim|gapura|tugu|bendungan|waduk|perlintasan|pos\s+polisi"
)
POLA_POI_ISYARAT = re.compile(   # patokan yang diawali kata penunjuk arah/posisi
    r"\b(?:depan|dekat|sebelah|samping|seberang|belakang|utara|selatan|timur|barat|turut|pinggir)"
    r"\s+(?:(?:di|pintu|masuk|gerbang|area|halaman|komplek|kompleks|kawasan)\s+)*"
    rf"(?P<v>(?:{KATA_POI})\b.*)",
    re.IGNORECASE,
)
POLA_POI_BEBAS = re.compile(rf"(?<!jl\.)(?<!jl)(?<!jalan)\s(?P<v>(?:{KATA_POI})\b.*)", re.IGNORECASE)
POLA_DUSUN = re.compile(r"\b(?:dusun|dsn|dukuh|dk)\b\.?\s*[:\-]?\s*(?P<v>[^,;\n()/]+)", re.IGNORECASE)

# Kata yang menandai AKHIR sebuah nama (jalan/desa/kecamatan/kabupaten).
# Contoh: "Kec. Cepu Kab. Blora" → nama kecamatan berhenti di kata "Kab".
KATA_HENTI = {
    "kab", "kabupaten", "kota", "kotamadya", "kodya", "kec", "kecamatan",
    "prov", "provinsi", "propinsi", "jawa", "jateng", "jatim", "jabar", "diy",
    "indonesia", "rt", "rw", "desa", "ds", "kel", "kelurahan", "dusun", "dsn",
    "dk", "dukuh", "polsek", "polres", "polresta", "polrestabes", "polda",
    "wilayah", "wil", "sekitar", "pukul", "jam", "tepatnya", "tepat", "arah",
    "jurusan", "km", "kilometer", "depan", "dekat", "sebelah", "samping",
    "ikut", "termasuk", "belakang",
    "seberang", "turut", "masuk", "simpang", "pertigaan", "perempatan", "no",
    "nomor", "kode", "kodepos", "yang", "dan", "antara", "tgl", "tanggal",
    "hari", "waktu", "lokasi", "tkp", "jalan", "jl", "jln", "ruas",
}
# Kata kunci alamat — dipakai untuk memutuskan apakah baris lanjutan masih
# bagian dari alamat TKP.
KATA_ALAMAT = re.compile(
    r"\b(?:jl|jln|jalan|ds|desa|kel|kelurahan|kec|kecamatan|kab|kabupaten|kota|"
    r"dusun|dsn|dk|dukuh|rt|rw|km|depan|dekat|simpang|turut|pertigaan|perempatan)\b",
    re.IGNORECASE,
)

# =============================================================================
# 2. UTILITAS TEKS
# =============================================================================
def _norm(teks) -> str:
    """Huruf kecil, buang tanda baca, rapikan spasi — untuk mencocokkan nama."""
    teks = str(teks or "").lower()
    teks = re.sub(r"[^a-z0-9]+", " ", teks)
    return re.sub(r"\s+", " ", teks).strip()


_AWALAN_WILAYAH = re.compile(
    r"^(?:kabupaten|kab|kota administrasi|kota adm|kotamadya|kodya|kota)\s+"
)


def _nama_dasar(teks) -> str:
    """'Kabupaten Blora' / 'KAB. BLORA' / 'Blora' → 'blora'."""
    return _AWALAN_WILAYAH.sub("", _norm(teks)).strip()


def bersihkan_teks(teks: str) -> str:
    """Seragamkan karakter aneh hasil PDF & rapikan spasi per baris."""
    teks = (teks or "").replace(" ", " ").replace("：", ":")
    teks = teks.replace("–", "-").replace("—", "-")
    baris = [re.sub(r"[ \t]+", " ", b).strip() for b in teks.splitlines()]
    return "\n".join(baris)


def potong_nama(mentah: str, maks_kata: int = 4) -> str:
    """Ambil nama bersih dari potongan teks: berhenti di kata henti/angka.

    'Cepu Kab. Blora Jawa Tengah' → 'Cepu'
    'KOTA KUDUS Kab. Kudus'       → 'Kota Kudus'  (kata pertama tidak dipotong)
    """
    hasil: list[str] = []
    for token in (mentah or "").split():
        kn = _norm(token)
        if not kn:                       # token tanda baca saja, misal "-"
            continue
        kata_awal = kn.split()[0]
        if hasil and (kata_awal in KATA_HENTI or re.fullmatch(r"\d+[a-z]?", kata_awal)):
            break
        bersih = token.strip(".,;:-'\"()")
        if bersih:
            hasil.append(bersih)
        if len(hasil) >= maks_kata:
            break
    return " ".join(hasil).title()


def _potong(teks: str, n: int) -> str:
    teks = str(teks or "")
    return teks if len(teks) <= n else teks[: n - 1].rstrip() + "…"


def _md(teks) -> str:
    """Escape karakter Markdown (termasuk $ yang memicu LaTeX di Streamlit)."""
    return re.sub(r"([\\`*_{}\[\]<>()#+!|$~])", r"\\\1", str(teks or ""))


def _fmt_km(km: float) -> str:
    return f"{km * 1000:.0f} m" if km < 1 else f"{km:.1f} km".replace(".", ",")


def _secret(nama: str, default: str = "") -> str:
    """Baca st.secrets dengan aman (tidak error bila secrets belum diisi)."""
    try:
        return str(st.secrets.get(nama, default))
    except Exception:
        return default


# =============================================================================
# 3. EKSTRAKSI PDF & PARSING LAPORAN POLISI
# =============================================================================
class DokumenTidakTerbaca(Exception):
    """Dokumen tidak bisa diambil teksnya — pesannya ditampilkan ke pengguna."""


def ekstrak_teks_pdf(isi_pdf: bytes) -> str:
    """Ambil teks dari beberapa halaman awal PDF LP."""
    with pdfplumber.open(io.BytesIO(isi_pdf)) as pdf:
        halaman = [(h.extract_text() or "") for h in pdf.pages[:MAKS_HALAMAN_PDF]]
    return bersihkan_teks("\n".join(halaman))


# --- Word .docx (Office Open XML: arsip zip berisi XML) -------------------------
_W = "{http://schemas.openxmlformats.org/wordprocessingml/2006/main}"
_MC_FALLBACK = "{http://schemas.openxmlformats.org/markup-compatibility/2006}Fallback"


_W2003 = b"http://schemas.microsoft.com/office/word/2003/wordml"
_W2006 = b"http://schemas.openxmlformats.org/wordprocessingml/2006/main"


def _anak_tabel(el, nama: str):
    """Baris/sel tabel, termasuk yang dibungkus content control (w:sdt)."""
    for a in el:
        if a.tag == _W + nama:
            yield a
        elif a.tag in (_W + "sdt", _W + "sdtContent", _W + "customXml"):
            yield from _anak_tabel(a, nama)


def _gabung_baris_tabel(sel: list[list[str]]) -> str:
    """Gabung sel-sel satu baris tabel menjadi baris teks.
    - Sel pendek (≤3 baris) digabung spasi: 'Tempat Kejadian | : | Jl...' →
      'Tempat Kejadian : Jl...' (satu baris, dikenali regex).
    - Sel panjang (mis. seluruh isi LP diketik di dalam satu sel besar) TIDAK
      dilebur, supaya tiap 'Label : isi' tetap di barisnya sendiri."""
    keluar, sekarang = [], []
    for baris_sel in sel:
        if len(baris_sel) <= 3:
            if baris_sel:
                sekarang.append(" ".join(baris_sel))
            continue
        sekarang.append(baris_sel[0])
        keluar.append(" ".join(sekarang))
        keluar.extend(baris_sel[1:-1])
        sekarang = [baris_sel[-1]]
    if sekarang:
        keluar.append(" ".join(sekarang))
    return "\n".join(b for b in keluar if b.strip())


def _teks_xml_word(xml_bytes: bytes) -> str:
    """Teks dari document.xml / header.xml. Paragraf → baris baru; baris TABEL →
    sel-selnya digabung dengan spasi, sehingga tabel 'Tempat Kejadian | : | Jl...'
    menjadi satu baris 'Tempat Kejadian : Jl...' yang dikenali regex."""
    root = ET.fromstring(xml_bytes)
    for induk in list(root.iter()):                 # buang duplikat textbox (mc:Fallback)
        for anak in list(induk):
            if anak.tag == _MC_FALLBACK:
                induk.remove(anak)

    def jalan(el, keping: list) -> None:
        for a in el:
            tag = a.tag
            if tag == _W + "t":
                keping.append(a.text or "")
            elif tag == _W + "tab":
                keping.append(" ")
            elif tag in (_W + "br", _W + "cr"):
                keping.append("\n")
            elif tag == _W + "noBreakHyphen":
                keping.append("-")
            elif tag == _W + "p":
                jalan(a, keping)
                keping.append("\n")
            elif tag == _W + "tbl":
                for baris in _anak_tabel(a, "tr"):
                    sel = []
                    for tc in _anak_tabel(baris, "tc"):
                        isi_sel: list = []
                        jalan(tc, isi_sel)
                        garis = (re.sub(r"\s+", " ", g).strip() for g in "".join(isi_sel).split("\n"))
                        sel.append([g for g in garis if g])
                    keping.append(_gabung_baris_tabel(sel) + "\n")
            elif tag in (_W + "delText", _W + "instrText", _W + "delInstrText"):
                continue                           # teks terhapus / kode field
            else:
                jalan(a, keping)

    keping: list = []
    jalan(root, keping)
    return "".join(keping)


def ekstrak_teks_wordxml(isi: bytes) -> str:
    """Word XML satu file: 'Word 2003 XML' atau 'Word XML Document' (flat)."""
    try:
        return _teks_xml_word(isi.replace(_W2003, _W2006))
    except ET.ParseError as err:
        raise DokumenTidakTerbaca("Dokumen Word XML rusak") from err


def ekstrak_teks_docx(isi: bytes) -> str:
    try:
        with zipfile.ZipFile(io.BytesIO(isi)) as z:
            nama = set(z.namelist())
            if "word/document.xml" not in nama:
                raise DokumenTidakTerbaca("File zip ini bukan dokumen Word")
            # Kop surat (mis. "RESOR GROBOGAN") sering ada di HEADER halaman → ikut dibaca.
            header = sorted(n for n in nama if re.fullmatch(r"word/header\d*\.xml", n))
            bagian = [_teks_xml_word(z.read(n)) for n in header]
            bagian.append(_teks_xml_word(z.read("word/document.xml")))
    except (zipfile.BadZipFile, ET.ParseError, KeyError) as err:
        raise DokumenTidakTerbaca(f"Dokumen Word rusak ({type(err).__name__})") from err
    return "\n".join(bagian)


# --- Word .doc lama (Word 97-2003, format biner OLE) -----------------------------
def _rapikan_teks_doc(t: str) -> str:
    """Karakter kendali Word biner → teks biasa. Kode field (mis. PAGE, HYPERLINK)
    dibuang, hanya hasil field yang dipertahankan."""
    keluar, tumpukan = [], []                 # tumpukan: True = sedang di bagian hasil field
    for ch in t:
        if ch == "\x13":
            tumpukan.append(False)
        elif ch == "\x14":
            if tumpukan:
                tumpukan[-1] = True
        elif ch == "\x15":
            if tumpukan:
                tumpukan.pop()
        elif all(tumpukan):
            keluar.append(ch)
    s = "".join(keluar)
    s = s.replace("\x07\x07", "\n").replace("\x07", " ")   # akhir sel & akhir baris tabel
    s = re.sub(r"[\r\x0b\x0c]", "\n", s)                   # paragraf, baris baru, halaman
    s = s.replace("\x1e", "-").replace("\x1f", "")
    return re.sub(r"[\x00-\x08\x0e-\x1d]", "", s)           # objek/gambar sisipan


def ekstrak_teks_doc(isi: bytes) -> str:
    """Baca .doc Word 97-2003 tanpa program luar: teks disusun dari 'piece table'
    (struktur CLX di stream 0Table/1Table) sesuai spesifikasi [MS-DOC]."""
    try:
        ole = olefile.OleFileIO(io.BytesIO(isi))
    except Exception as err:
        raise DokumenTidakTerbaca(f"Dokumen Word .doc rusak ({type(err).__name__})") from err
    try:
        if not ole.exists("WordDocument"):
            raise DokumenTidakTerbaca("File .doc ini bukan dokumen Word (mungkin Excel/lainnya)")
        wd = ole.openstream("WordDocument").read()
        ident, nfib = struct.unpack_from("<HH", wd, 0)
        flags = struct.unpack_from("<H", wd, 0x0A)[0]
        if ident != 0xA5EC:
            raise DokumenTidakTerbaca("Struktur dokumen Word tidak dikenali")
        # Word 97-2003 = nFib 0x00C1 (0x00C0: 'dokumen baru kosong' Windows, 0x00C2:
        # Word 97 BiDi). Di bawah itu Word 6/95 yang strukturnya berbeda.
        if nfib < 0x00C0:
            raise DokumenTidakTerbaca("Format Word 6/95 (sangat lama) — buka di Word lalu "
                                      "simpan ulang sebagai .docx")
        if flags & 0x0100:
            raise DokumenTidakTerbaca("Dokumen Word terkunci password — buka kuncinya dulu")
        nama_tabel = "1Table" if flags & 0x0200 else "0Table"
        if not ole.exists(nama_tabel):
            raise DokumenTidakTerbaca("Struktur dokumen Word tidak lengkap")
        tabel = ole.openstream(nama_tabel).read()
    finally:
        ole.close()

    try:
        # Lokasi fcClx/lcbClx dihitung dari panjang tiap bagian FIB (bukan offset tetap).
        pos = 0x20
        csw = struct.unpack_from("<H", wd, pos)[0]
        pos += 2 + csw * 2
        cslw = struct.unpack_from("<H", wd, pos)[0]
        pos += 2 + cslw * 4
        pos += 2                                            # cbRgFcLcb
        fc_clx, lcb_clx = struct.unpack_from("<II", wd, pos + 33 * 8)
        clx = tabel[fc_clx: fc_clx + lcb_clx]
        i = 0
        while i < len(clx) and clx[i] == 0x01:              # lewati Prc (format)
            i += 3 + struct.unpack_from("<H", clx, i + 1)[0]
        if i >= len(clx) or clx[i] != 0x02:
            raise DokumenTidakTerbaca("Struktur teks dokumen Word tidak dikenali")
        lcb = struct.unpack_from("<I", clx, i + 1)[0]
        plc = clx[i + 5: i + 5 + lcb]
        n = (lcb - 4) // 12
        cp = struct.unpack_from(f"<{n + 1}I", plc, 0)
        keping = []
        for k in range(n):
            fc_mentah = struct.unpack_from("<I", plc, (n + 1) * 4 + k * 8 + 2)[0]
            jumlah = cp[k + 1] - cp[k]
            if fc_mentah & 0x40000000:                      # teks 8-bit (cp1252)
                awal = (fc_mentah & 0x3FFFFFFF) // 2
                keping.append(wd[awal: awal + jumlah].decode("cp1252", errors="replace"))
            else:                                           # teks UTF-16
                awal = fc_mentah & 0x3FFFFFFF
                keping.append(wd[awal: awal + 2 * jumlah].decode("utf-16-le", errors="replace"))
    except struct.error as err:
        raise DokumenTidakTerbaca("Dokumen Word .doc rusak / terpotong") from err
    return _rapikan_teks_doc("".join(keping))


# --- RTF & HTML (sering disimpan dengan akhiran .doc oleh sistem lain) ----------
_RTF_TOKEN = re.compile(
    r"\\([a-z]{1,32})(-?\d{1,10})?[ ]?|\\'([0-9a-f]{2})|\\([^a-z])|([{}])|[\r\n]+|(.)",
    re.IGNORECASE | re.DOTALL,
)
_RTF_DILEWATI = {
    "fonttbl", "colortbl", "stylesheet", "info", "pict", "object", "themedata",
    "colorschememapping", "latentstyles", "datastore", "xmlnstbl", "listtable",
    "listoverridetable", "rsidtbl", "generator", "fldinst", "filetbl", "revtbl",
    "mmathpr", "pgdsctbl", "bkmkstart", "bkmkend", "footnote", "atnid", "atnauthor",
}
_RTF_KHUSUS = {"par": "\n", "line": "\n", "sect": "\n", "page": "\n", "row": "\n",
               "nestrow": "\n", "cell": " ", "nestcell": " ", "tab": " ",
               "emdash": "-", "endash": "-", "lquote": "'", "rquote": "'",
               "ldblquote": '"', "rdblquote": '"', "bullet": "•"}


def ekstrak_teks_rtf(isi: bytes) -> str:
    teks = isi.decode("latin-1")
    tumpukan, abaikan, uc_lewat, sisa_lewat, keluar = [], False, 1, 0, []
    for m in _RTF_TOKEN.finditer(teks):
        kata, arg, heks, karakter, kurung, biasa = m.groups()
        if kurung:
            sisa_lewat = 0
            if kurung == "{":
                tumpukan.append((uc_lewat, abaikan))
            elif tumpukan:
                uc_lewat, abaikan = tumpukan.pop()
        elif karakter:
            sisa_lewat = 0
            if karakter == "*":
                abaikan = True
            elif abaikan:
                continue
            elif karakter == "~":
                keluar.append(" ")                      # spasi tak terputus
            elif karakter == "_":
                keluar.append("-")                      # tanda hubung tak terputus
            elif karakter in "\r\n":
                keluar.append("\n")                     # '\' + enter = \par
            elif karakter in "{}\\":
                keluar.append(karakter)
        elif kata:
            sisa_lewat = 0
            kata = kata.lower()
            if kata in _RTF_DILEWATI:
                abaikan = True
            elif abaikan:
                continue
            elif kata in _RTF_KHUSUS:
                keluar.append(_RTF_KHUSUS[kata])
            elif kata == "uc":
                uc_lewat = int(arg or 1)
            elif kata == "u" and arg:
                kode = int(arg)
                keluar.append(chr(kode + 0x10000 if kode < 0 else kode))
                sisa_lewat = uc_lewat
        elif heks:
            if sisa_lewat > 0:
                sisa_lewat -= 1
            elif not abaikan:
                keluar.append(bytes([int(heks, 16)]).decode("cp1252", errors="replace"))
        elif biasa:
            if sisa_lewat > 0:
                sisa_lewat -= 1
            elif not abaikan:
                keluar.append(biasa)
    return "".join(keluar)


class _PembacaHTML(HTMLParser):
    """HTML → teks. Tabel diperlakukan sama seperti tabel Word (_gabung_baris_tabel):
    satu baris tabel pendek = satu baris teks; sel besar tetap dipecah per baris.
    Tahan terhadap HTML lama yang tidak menutup </td> / </tr>."""
    BLOK = {"p", "div", "br", "li", "h1", "h2", "h3", "h4", "h5", "h6", "title"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self._lewati = 0
        self._penampung = [[]]       # tumpukan buffer teks (paling dasar = dokumen)
        self._tabel = []             # tumpukan tabel; tiap tabel menyimpan baris aktifnya

    def _tulis(self, s):
        self._penampung[-1].append(s)

    def _tutup_sel(self, t):
        b = t["baris"]
        if b and b["buka"]:
            isi = "".join(self._penampung.pop())
            b["sel"].append([g for g in (re.sub(r"\s+", " ", x).strip() for x in isi.split("\n")) if g])
            b["buka"] = False

    def _tutup_baris(self, t):
        if t["baris"]:
            self._tutup_sel(t)
            self._tulis(_gabung_baris_tabel(t["baris"]["sel"]) + "\n")
            t["baris"] = None

    def _tabel_aktif(self):
        if not self._tabel:
            self._tabel.append({"baris": None})
        return self._tabel[-1]

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style", "head"):
            self._lewati += 1
        elif tag == "table":
            self._tulis("\n")
            self._tabel.append({"baris": None})
        elif tag == "tr":
            t = self._tabel_aktif()
            self._tutup_baris(t)
            t["baris"] = {"sel": [], "buka": False}
        elif tag in ("td", "th"):
            t = self._tabel_aktif()
            if t["baris"] is None:
                t["baris"] = {"sel": [], "buka": False}
            self._tutup_sel(t)
            self._penampung.append([])
            t["baris"]["buka"] = True
        elif tag in self.BLOK:
            self._tulis("\n")

    def handle_endtag(self, tag):
        if tag in ("script", "style", "head"):
            self._lewati = max(0, self._lewati - 1)
        elif tag in ("td", "th"):
            if self._tabel:
                self._tutup_sel(self._tabel[-1])
        elif tag == "tr":
            if self._tabel:
                self._tutup_baris(self._tabel[-1])
        elif tag == "table":
            if self._tabel:
                self._tutup_baris(self._tabel.pop())
            self._tulis("\n")
        elif tag in self.BLOK:
            self._tulis("\n")

    def handle_data(self, data):
        if not self._lewati:
            self._tulis(re.sub(r"\s+", " ", data))

    def hasil(self) -> str:
        while self._tabel:                     # tutup tabel/sel yang tidak ditutup
            self._tutup_baris(self._tabel.pop())
        while len(self._penampung) > 1:
            sisa = self._penampung.pop()
            self._penampung[-1].extend(sisa)
        return "".join(self._penampung[0])


def ekstrak_teks_html(isi: bytes, charset: str | None = None) -> str:
    m = re.search(rb"charset=[\"']?([a-z0-9_\-]+)", isi[:4096], re.IGNORECASE)
    kode = charset or (m.group(1).decode() if m else "utf-8")
    try:
        teks = isi.decode(kode, errors="replace")
    except LookupError:
        teks = isi.decode("utf-8", errors="replace")
    p = _PembacaHTML()
    p.feed(teks)
    p.close()
    return p.hasil()


def ekstrak_teks_mht(isi: bytes) -> str:
    """'Halaman web arsip tunggal' (.mht/.mhtml) — kadang diberi akhiran .doc."""
    pesan = email.message_from_bytes(isi, policy=email.policy.default)
    for bagian in pesan.walk():
        if bagian.get_content_type() == "text/html":
            return ekstrak_teks_html(bagian.get_payload(decode=True) or b"",
                                     bagian.get_content_charset())
    raise DokumenTidakTerbaca("File MHT ini tidak berisi dokumen")


def jenis_dokumen(isi: bytes) -> str:
    """Kenali format dari ISI file (bukan dari akhiran nama file) — sistem lain
    sering menyimpan RTF / HTML / XML dengan akhiran .doc."""
    if b"%PDF-" in isi[:1024]:
        return "pdf"
    if isi[:4] == b"PK\x03\x04":
        return "docx"
    if isi[:8] == b"\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1":
        return "doc"
    kepala = isi[:4096].lstrip(b"\xef\xbb\xbf \r\n\t").lower()
    if kepala.startswith(b"{\\rtf"):
        return "rtf"
    if b"mime-version:" in kepala[:1024] and b"multipart/related" in kepala:
        return "mht"
    if kepala.startswith(b"<") and (_W2003 in isi[:20000] or
                                    (_W2006 in isi[:20000] and b"<html" not in kepala)):
        return "wordxml"
    if any(t in kepala for t in (b"<html", b"<!doctype html", b"<body", b"<table")):
        return "html"
    return ""


def ekstrak_teks(isi: bytes) -> tuple[str, str]:
    """(teks, jenis) dari PDF / Word .docx / Word .doc / RTF / HTML / MHT / Word XML."""
    jenis = jenis_dokumen(isi)
    if not jenis:
        raise DokumenTidakTerbaca("Format file tidak dikenali (bukan PDF/Word)")
    pembaca = {"pdf": ekstrak_teks_pdf, "docx": ekstrak_teks_docx, "doc": ekstrak_teks_doc,
               "rtf": ekstrak_teks_rtf, "html": ekstrak_teks_html, "mht": ekstrak_teks_mht,
               "wordxml": ekstrak_teks_wordxml}[jenis]
    teks = pembaca(isi)
    return bersihkan_teks(teks[:300_000]), jenis


# --- Pola regex ---------------------------------------------------------------
# Label baris TKP, contoh: "2. Tempat Kejadian : Jl. Raya ...", "TKP : ...",
# "Lokasi Kejadian : ...". Isi boleh kosong (alamat lanjut di baris berikutnya).
POLA_LABEL_TKP = re.compile(
    r"^(?:\d{1,2}\s*[.)]\s*)?(?:[a-z]\s*[.)]\s*)?"
    r"(?:tempat\s+kejadian(?:\s+perkara)?|lokasi\s+kejadian(?:\s+perkara)?|"
    r"lokasi\s+tkp|t\s*\.?\s*k\s*\.?\s*p\s*\.?|lokasi)"
    r"\s*(?:\([^)]*\))?\s*:\s*(?P<isi>.*)$",
    re.IGNORECASE,
)
# Label umum "Sesuatu :" — menandai baris berikutnya sudah bukan alamat TKP.
POLA_LABEL_UMUM = re.compile(
    r"^(?:\d{1,2}\s*[.)]\s*)?(?:[a-z]\s*[.)]\s*)?[a-z][a-z /.\-]{1,40}\s*:",
    re.IGNORECASE,
)
POLA_BARIS_BERNOMOR = re.compile(r"^\d{1,2}\s*[.)]\s+\S")

# Kalimat kronologi: "telah terjadi laka lantas di Jl. ... Kec. ... Kab. ..."
# (diambil maks. 220 karakter, lalu dipotong di kata sambung — BUKAN di titik,
#  karena alamat penuh singkatan bertitik seperti "Ds." dan "Kec.")
POLA_KRONOLOGI = re.compile(
    r"(?:terjadi|kejadian)[^.\n]{0,80}?\bdi\s+(?P<isi>(?:jl|jln|jalan)\b.{5,220})",
    re.IGNORECASE,
)
POLA_AKHIR_KRONOLOGI = re.compile(
    r"\s+(?:antara|yang|ketika|saat|pada|dengan|melibatkan|kemudian|selanjutnya|"
    r"akibat|sehingga|adapun)\b",
    re.IGNORECASE,
)

POLA_KEC = re.compile(r"\bkec(?:amatan\b|\.|\b)\s*[:\-]?\s*(?P<v>[^,;\n()/]+)", re.IGNORECASE)
POLA_DESA = re.compile(
    r"\b(?:desa|ds|kelurahan|kel)\b\.?\s*[:\-]?\s*(?P<v>[^,;\n()/]+)", re.IGNORECASE
)
POLA_JALAN = re.compile(r"\b(?:jalan|jln|jl)\b\.?\s*(?P<v>[^,;\n()]+)", re.IGNORECASE)
# Urutan penting: "Kab/Kota" dulu, lalu "Kab", terakhir "Kota".
POLA_KAB = [
    (re.compile(r"\bkab(?:upaten)?\.?\s*/\s*kota\b\s*[:\-]?\s*(?P<v>[^,;\n()/]+)", re.I), ""),
    (re.compile(r"\bkab(?:upaten\b|\.|\b)\s*[:\-]?\s*(?P<v>[^,;\n()/]+)", re.I), "Kabupaten"),
    (re.compile(r"\b(?:kotamadya|kodya|kota)\b\.?\s*[:\-]?\s*(?P<v>[^,;\n()/]+)", re.I), "Kota"),
]
POLA_PATOKAN = re.compile(   # berhenti sebelum nama desa/kecamatan/kabupaten
    r"\b(?:depan|dekat|sebelah|samping|seberang|turut|tepatnya|km\.?\s*\d+|kilometer|"
    r"simpang|pertigaan|perempatan|jembatan|spbu|pasar|masjid|sekolah)\b"
    r"(?:(?!\b(?:ds|dsn|dusun|desa|kel|kelurahan|kec|kecamatan|kab|kabupaten|kota|rt|rw|ikut|"
    r"termasuk|wilayah)\b)[^,;\n]){0,60}",
    re.IGNORECASE,
)
POLA_NO_LP = re.compile(r"\b(LP\s*/\s*[A-Z0-9][^\n]{2,140})", re.IGNORECASE)
POLA_WAKTU = re.compile(
    r"^(?:\d{1,2}\s*[.)]\s*)?(?:waktu\s+kejadian|hari\s*/\s*tanggal|hari\s*/\s*tgl|"
    r"tanggal\s+kejadian|waktu)\s*:\s*(?P<v>.+)$",
    re.IGNORECASE | re.MULTILINE,
)
POLA_POLRES = re.compile(r"\bpolres(?P<t>tabes|ta)?\b\.?\s+(?P<v>[a-z][a-z ]{2,40})", re.IGNORECASE)
# Kop surat resmi: "... DAERAH JAWA TENGAH RESOR BLORA" / "RESOR KOTA SURAKARTA"
POLA_RESOR = re.compile(r"\bresor\s+(?P<t>kota\s+(?:besar\s+)?)?(?P<v>[a-z][a-z ]{2,40})", re.IGNORECASE)
POLA_AWALAN_JALAN = re.compile(r"^(?:jalan|jln|jl)\b\.?\s*", re.IGNORECASE)
POLA_AWALAN_KEC = re.compile(r"^kec(?:amatan\b|\.|\b)\s*", re.IGNORECASE)
POLA_AWALAN_DESA = re.compile(r"^(?:desa|ds|kelurahan|kel)\b\.?\s*", re.IGNORECASE)


def _ambil_blok_tkp(teks: str) -> str:
    """Ambil isi 'Tempat Kejadian' + maksimal 3 baris lanjutan alamat."""
    baris = teks.splitlines()
    for i, b in enumerate(baris):
        m = POLA_LABEL_TKP.match(b)
        if not m:
            continue
        bagian = [m.group("isi").strip()] if m.group("isi").strip() else []
        for lanjut in baris[i + 1 : i + 6]:
            if len(bagian) >= 4:
                break
            if not lanjut.strip():
                if bagian:
                    break
                continue
            if POLA_LABEL_UMUM.match(lanjut) or POLA_BARIS_BERNOMOR.match(lanjut):
                break
            # Baris lanjutan hanya diterima bila memang berbau alamat.
            if bagian and not KATA_ALAMAT.search(lanjut):
                break
            bagian.append(lanjut.strip())
        blok = " ".join(bagian).strip(" :-")
        if blok:
            return re.sub(r"^(?:di|pada)\s+", "", blok, flags=re.IGNORECASE)
    return ""


def _ambil_label(teks: str, pola_label: str) -> str:
    """Isian berlabel di awal baris, misal 'Kecamatan : CEPU' (format IRSMS).
    Baris yang mengandung kata 'alamat' (alamat pelapor/korban) DILEWATI agar
    alamat rumah korban tidak dikira lokasi kejadian."""
    pola = re.compile(
        rf"^(?:\d{{1,2}}\s*[.)]\s*)?(?:{pola_label})\s*:\s*(?P<isi>.+)$", re.IGNORECASE
    )
    for b in teks.splitlines():
        if "alamat" in b.lower():
            continue
        m = pola.match(b)
        if m and m.group("isi").strip(" -.:"):
            return m.group("isi").strip()
    return ""


def ambil_poi(teks: str) -> str:
    """Nama patokan yang bisa dicari di peta, mis. 'depan Pasar Tempel ikut wilayah'
    → 'Pasar Tempel'. Harus berupa jenis tempat + nama (minimal 2 kata)."""
    for pola in (POLA_POI_ISYARAT, POLA_POI_BEBAS):
        for m in pola.finditer(teks or ""):
            hasil = []
            for token in m.group("v").split():
                kn = _norm(token)
                if not kn:
                    continue
                if hasil and (kn.split()[0] in KATA_HENTI or kn.split()[0] == "wilayah"):
                    break
                bersih = token.strip(".,;:'\"()“”‘’")
                if bersih:
                    hasil.append(bersih if bersih.isupper() and len(bersih) <= 5 else bersih.title())
                if len(hasil) >= 4 or token.endswith((",", ";")):
                    break
            if len(hasil) >= 2:
                return " ".join(hasil)
    return ""


def _cari_kabupaten(teks: str) -> tuple[str, str]:
    """Kembalikan (nama, jenis) kabupaten/kota dari potongan teks alamat."""
    for pola, jenis in POLA_KAB:
        for m in pola.finditer(teks):
            nama = potong_nama(m.group("v"))
            if nama and _norm(nama) not in KATA_HENTI:
                return nama, jenis
    return "", ""


def parse_lp(teks: str) -> dict:
    """Ekstrak field penting dari teks LP. Semua nama wilayah HANYA diambil
    dari blok TKP (atau isian berlabel / kronologi), tidak dari alamat korban."""
    info = {
        "no_lp": "", "waktu": "", "polres": "", "tkp": "", "sumber_tkp": "",
        "jalan": "", "poi": "", "dusun": "", "desa": "", "kecamatan": "", "kabupaten": "",
        "jenis_wilayah": "", "sumber_wilayah": "", "patokan": "",
    }

    m = POLA_NO_LP.search(teks)
    if m:
        info["no_lp"] = re.sub(r"\s{2,}", " ", m.group(1)).strip(" .,;")
    m = POLA_WAKTU.search(teks)
    if m:
        info["waktu"] = _potong(m.group("v").strip(), 100)

    # Polres penangan → petunjuk kabupaten/kota bila TKP tidak menyebutnya.
    polres_nama, polres_jenis = "", ""
    m = POLA_POLRES.search(teks) or POLA_RESOR.search(teks)
    if m:
        polres_nama = re.sub(r"^metro\s+", "", potong_nama(m.group("v"), 3), flags=re.I)
        polres_jenis = "Kota" if m.group("t") else ""
        info["polres"] = f"Polres{'ta' if polres_jenis else ''} {polres_nama}".strip()

    # --- Blok TKP: label "Tempat Kejadian" → kalimat kronologi → isian berlabel
    tkp = _ambil_blok_tkp(teks)
    if tkp:
        info["sumber_tkp"] = "Blok 'Tempat Kejadian'"
    else:
        m = POLA_KRONOLOGI.search(re.sub(r"\s+", " ", teks))
        if m:
            tkp = POLA_AKHIR_KRONOLOGI.split(m.group("isi"), maxsplit=1)[0].strip(" .,")
            info["sumber_tkp"] = "Kalimat kronologi"
    info["tkp"] = tkp

    if tkp:
        m = POLA_JALAN.search(tkp)
        if m:
            # "Jalan Umum jurusan Danyang - Banjarsari" → "Jalan Danyang Banjarsari"
            nama_jl = potong_nama(POLA_KATA_SAMPAH_JALAN.sub(" ", m.group("v")), maks_kata=6)
            info["jalan"] = f"Jalan {nama_jl}" if nama_jl else ""
        info["poi"] = ambil_poi(tkp)
        m = POLA_DUSUN.search(tkp)
        if m:
            info["dusun"] = potong_nama(m.group("v"))
        m = POLA_DESA.search(tkp)
        if m:
            info["desa"] = potong_nama(m.group("v"))
        m = POLA_KEC.search(tkp)
        if m:
            info["kecamatan"] = potong_nama(m.group("v"))
        info["kabupaten"], info["jenis_wilayah"] = _cari_kabupaten(tkp)
        if info["kabupaten"]:
            info["sumber_wilayah"] = info["sumber_tkp"]
        patokan = [p.group(0).strip() for p in POLA_PATOKAN.finditer(tkp)][:2]
        info["patokan"] = " · ".join(patokan)

    # Format isian berlabel (IRSMS): hanya dipakai untuk field yang masih kosong.
    # Awalan seperti "JL." / "KEC." / "KAB." dibuang agar query geocoding bersih.
    if not info["jalan"]:
        isi = POLA_AWALAN_JALAN.sub("", _ambil_label(teks, r"nama\s+jalan|ruas\s+jalan"))
        jl = potong_nama(POLA_KATA_SAMPAH_JALAN.sub(" ", isi), maks_kata=6)
        info["jalan"] = f"Jalan {jl}" if jl else ""
    if not info["desa"]:
        isi = _ambil_label(teks, r"desa\s*/\s*kel(?:urahan)?\.?|kelurahan\s*/\s*desa|kelurahan|desa")
        info["desa"] = potong_nama(POLA_AWALAN_DESA.sub("", isi))
    if not info["kecamatan"]:
        isi = _ambil_label(teks, r"kecamatan|kec\.")
        info["kecamatan"] = potong_nama(POLA_AWALAN_KEC.sub("", isi))
    if not info["kabupaten"]:
        isi = _ambil_label(teks, r"kab(?:upaten)?\.?\s*/\s*kota|kabupaten|kab\.|kota(?:madya)?")
        if isi:
            nama, jenis = _cari_kabupaten(isi)          # isi "KAB. BLORA" → Blora
            info["kabupaten"] = nama or potong_nama(isi)
            info["jenis_wilayah"] = jenis
            info["sumber_wilayah"] = "Isian berlabel di LP"
    if not info["tkp"]:
        bagian = [info["jalan"], info["desa"], info["kecamatan"], info["kabupaten"]]
        info["tkp"] = ", ".join(b for b in bagian if b)
        if info["tkp"]:
            info["sumber_tkp"] = "Isian berlabel di LP"

    # Fallback terakhir untuk kabupaten: nama Polres di kop/nomor LP.
    if not info["kabupaten"] and polres_nama:
        info["kabupaten"], info["jenis_wilayah"] = polres_nama, polres_jenis
        info["sumber_wilayah"] = f"Wilayah {info['polres']} (TKP tidak menyebut kab/kota)"
    return info


# =============================================================================
# 4. GEOMETRI (Python murni — tanpa shapely, ringan untuk Streamlit Cloud)
# =============================================================================
def haversine_km(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    """Jarak garis lurus di permukaan bumi (km)."""
    r = 6371.0088
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = p2 - p1, math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


def _daftar_poligon(geojson: dict) -> list:
    tipe, koordinat = geojson.get("type"), geojson.get("coordinates") or []
    if tipe == "Polygon":
        return [koordinat]
    if tipe == "MultiPolygon":
        return koordinat
    return []


def _dalam_ring(x: float, y: float, ring: list) -> bool:
    """Ray casting: apakah titik (x=lon, y=lat) di dalam satu ring poligon."""
    dalam, j = False, len(ring) - 1
    for i in range(len(ring)):
        xi, yi = ring[i][0], ring[i][1]
        xj, yj = ring[j][0], ring[j][1]
        if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / (yj - yi) + xi:
            dalam = not dalam
        j = i
    return dalam


def _jarak_ke_segmen(px, py, ax, ay, bx, by) -> float:
    dx, dy = bx - ax, by - ay
    if dx == 0 and dy == 0:
        return math.hypot(px - ax, py - ay)
    t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy)))
    return math.hypot(px - (ax + t * dx), py - (ay + t * dy))


def titik_dalam_wilayah(lat: float, lon: float, geojson: dict,
                        toleransi_km: float = TOLERANSI_BATAS_KM) -> bool:
    """True bila titik di dalam poligon wilayah, atau ≤ toleransi_km dari batasnya
    (jalan yang persis di garis batas kabupaten tetap dianggap sah)."""
    poligon = _daftar_poligon(geojson or {})
    for rings in poligon:
        if rings and _dalam_ring(lon, lat, rings[0]) and not any(
            _dalam_ring(lon, lat, lubang) for lubang in rings[1:]
        ):
            return True
    if toleransi_km <= 0:
        return False
    # Proyeksi equirectangular lokal (akurat untuk jarak < beberapa km).
    kx, ky = 111.320 * math.cos(math.radians(lat)), 110.574
    dlat, dlon = toleransi_km / ky, toleransi_km / max(kx, 1e-6)
    px, py = lon * kx, lat * ky
    for rings in poligon:
        for ring in rings:
            for a, b in zip(ring, ring[1:]):
                if (min(a[1], b[1]) - dlat > lat or max(a[1], b[1]) + dlat < lat
                        or min(a[0], b[0]) - dlon > lon or max(a[0], b[0]) + dlon < lon):
                    continue                      # segmen jauh, lewati (cepat)
                if _jarak_ke_segmen(px, py, a[0] * kx, a[1] * ky, b[0] * kx, b[1] * ky) <= toleransi_km:
                    return True
    return False


def dalam_indonesia(lat: float, lon: float) -> bool:
    la0, la1, lo0, lo1 = BATAS_INDONESIA
    return la0 <= lat <= la1 and lo0 <= lon <= lo1


def parse_koordinat(teks: str):
    """'-6.89, 110.63' atau link Google Maps '...@-6.89,110.63,17z' → (lat, lon)."""
    if not teks:
        return None
    t = urllib.parse.unquote(teks)
    m = (re.search(r"@(-?\d{1,3}\.\d+),\s*(-?\d{1,3}\.\d+)", t)
         or re.search(r"(-?\d{1,3}\.\d+)\s*[,; ]\s*(-?\d{1,3}\.\d+)", t))
    if not m:
        return None
    lat, lon = float(m.group(1)), float(m.group(2))
    if not dalam_indonesia(lat, lon) and dalam_indonesia(lon, lat):
        lat, lon = lon, lat                       # pengguna tertukar urutan
    return (lat, lon) if dalam_indonesia(lat, lon) else None


# =============================================================================
# 5. GEOCODING BERLAPIS ANTI-"NYASAR" (Nominatim via geopy)
# =============================================================================
class NominatimTKP(Nominatim):
    """Nominatim + `polygon_threshold`: poligon batas wilayah disederhanakan
    (±50 m) supaya respons tetap ringan — cukup untuk uji "di dalam kabupaten"."""

    def _construct_url(self, base_api, params):
        if params.get("polygon_geojson"):
            params = {**params, "polygon_threshold": 0.0005}
        return super()._construct_url(base_api, params)


@st.cache_resource(show_spinner=False)
def _geocoder():
    """Satu instance per server. RateLimiter menjaga ≤ 1 permintaan/detik sesuai
    kebijakan Nominatim. Error koneksi DILEMPAR (tidak ditelan) supaya kegagalan
    jaringan tidak ikut tersimpan di cache sebagai 'tidak ditemukan'."""
    ua = _secret("NOMINATIM_USER_AGENT", "jr-survei-tkp/1.0 (aplikasi internal survei klaim)")
    geolocator = NominatimTKP(user_agent=ua, timeout=20)
    return RateLimiter(
        geolocator.geocode, min_delay_seconds=1.1, max_retries=2,
        error_wait_seconds=4.0, swallow_exceptions=False,
    )


@st.cache_data(show_spinner=False, ttl=7 * 24 * 3600, max_entries=20000)
def nominatim_cari(query: str, limit: int = 5, viewbox: tuple | None = None,
                   poligon: bool = False) -> list[dict]:
    """Panggil Nominatim (hasil di-cache 7 hari → proses ulang jadi instan)."""
    opsi = dict(exactly_one=False, limit=limit, country_codes="id",
                addressdetails=True, namedetails=True, language="id")
    if viewbox:
        lat_min, lat_max, lon_min, lon_max = viewbox
        opsi.update(viewbox=[(lat_min, lon_min), (lat_max, lon_max)], bounded=True)
    if poligon:
        opsi["geometry"] = "geojson"
    hasil = _geocoder()(query, **opsi)
    return [lokasi.raw for lokasi in (hasil or [])]


_KUNCI_ADMIN = ("county", "city", "municipality", "regency", "state_district",
                "city_district", "town", "village", "suburb")


def _luas_bbox(raw: dict) -> float:
    try:
        s, n, w, e = (float(x) for x in raw.get("boundingbox", []))
        return max(n - s, 0.0) * max(e - w, 0.0)
    except (TypeError, ValueError):
        return 0.0


def pilih_poligon_wilayah(kandidat: list[dict], nama: str, jenis: str):
    """Pilih poligon kabupaten/kota yang paling cocok dari hasil Nominatim.

    Syarat: batas administratif + geometri poligon + nama SAMA PERSIS.
    Skor: cocok jenis (Kabupaten vs Kota) > luas wilayah (kabupaten lebih luas
    dari kecamatan bernama sama, misal Kab. Blora vs Kec. Blora) > urutan.
    """
    target = _nama_dasar(nama)
    terbaik, skor_terbaik = None, -math.inf
    for urutan, raw in enumerate(kandidat):
        if raw.get("class") != "boundary" or raw.get("type") != "administrative":
            continue
        if (raw.get("geojson") or {}).get("type") not in ("Polygon", "MultiPolygon"):
            continue
        alamat = raw.get("address") or {}
        if alamat and not any(k in alamat for k in _KUNCI_ADMIN):
            continue                                  # level provinsi/negara
        nd = raw.get("namedetails") or {}
        nama_osm = [str(v) for k, v in nd.items()
                    if k in ("name", "official_name", "name:id", "alt_name", "short_name")]
        if not nama_osm:
            nama_osm = [str(raw.get("display_name", "")).split(",")[0]]
        if not any(_nama_dasar(n) == target for n in nama_osm):
            continue
        gabung = " | ".join(_norm(n) for n in nama_osm)
        if re.search(r"\b(?:kecamatan|kelurahan|desa)\b", gabung):
            continue                                  # jelas bukan kab/kota
        ada_kab = bool(re.search(r"\b(?:kabupaten|kab)\b", gabung))
        ada_kota = bool(re.search(r"\bkota\b", gabung))
        skor = 0.0
        if jenis == "Kabupaten":
            skor += 10 if ada_kab else (-10 if ada_kota else 0)
        elif jenis == "Kota":
            skor += 10 if ada_kota else (-10 if ada_kab else 0)
        skor += math.log10(_luas_bbox(raw) + 1e-6) - urutan * 0.05
        if skor > skor_terbaik:
            terbaik, skor_terbaik = raw, skor
    return terbaik


@st.cache_data(show_spinner=False, ttl=30 * 24 * 3600, max_entries=1000)
def cari_wilayah(nama: str, jenis: str):
    """Cari poligon batas kabupaten/kota TKP (di-cache 30 hari)."""
    if jenis == "Kota":
        daftar_query = [f"Kota {nama}", nama]
    elif jenis == "Kabupaten":
        daftar_query = [f"Kabupaten {nama}", nama]
    else:
        daftar_query = [nama, f"Kabupaten {nama}", f"Kota {nama}"]
    kandidat, sudah = [], set()
    for q in daftar_query:
        for raw in nominatim_cari(q, limit=8, poligon=True):
            kunci = (raw.get("osm_type"), raw.get("osm_id"))
            if kunci not in sudah:
                sudah.add(kunci)
                kandidat.append(raw)
    raw = pilih_poligon_wilayah(kandidat, nama, jenis)
    if raw is None:
        return None
    return {"bbox": _bbox_raw(raw), "geojson": raw["geojson"],
            "display_name": raw.get("display_name", ""),
            "osm": (raw.get("osm_type"), str(raw.get("osm_id")))}


def _bbox_raw(raw: dict) -> tuple:
    s, n, w, e = (float(x) for x in raw["boundingbox"])
    return (s, n, w, e)


def _perlebar(bbox: tuple, derajat: float) -> tuple:
    s, n, w, e = bbox
    return (s - derajat, n + derajat, w - derajat, e + derajat)


def _nama_kec(teks) -> str:
    return re.sub(r"^(?:kecamatan|kec)\s+", "", _norm(teks)).strip()


@st.cache_data(show_spinner=False, ttl=30 * 24 * 3600, max_entries=5000)
def cari_kecamatan(kec: str, kab: str, jenis: str):
    """Lokasi kecamatan TKP — HANYA yang berada di dalam kab/kota TKP.
    Mengembalikan titik pusat + poligon batas kecamatan (bila tersedia di OSM).
    Dipakai untuk (1) lapis terakhir 'pusat kecamatan' dan (2) memastikan hasil
    jalan/patokan/desa memang dekat kecamatan yang tertulis di LP."""
    wilayah = cari_wilayah(kab, jenis)
    viewbox = _perlebar(wilayah["bbox"], 0.02) if wilayah else None
    target = _nama_kec(kec)
    poligon, titik = None, None
    for raw in nominatim_cari(f"{kec}, {kab}", limit=8, viewbox=viewbox, poligon=True):
        if raw.get("class") not in ("boundary", "place"):
            continue
        nd = raw.get("namedetails") or {}
        nama_osm = [str(v) for k, v in nd.items()
                    if k in ("name", "official_name", "name:id", "alt_name", "short_name")]
        if not nama_osm:
            nama_osm = [str(raw.get("display_name", "")).split(",")[0]]
        if not any(_nama_kec(n) == target for n in nama_osm):
            continue
        lat, lon = float(raw["lat"]), float(raw["lon"])
        if wilayah:
            if (raw.get("osm_type"), str(raw.get("osm_id"))) == wilayah.get("osm"):
                continue                       # itu kabupatennya sendiri (Kec. Blora vs Kab. Blora)
            if _luas_bbox(raw) >= 0.6 * _luas_bbox({"boundingbox": wilayah["bbox"]}):
                continue
            if not titik_dalam_wilayah(lat, lon, wilayah["geojson"]):
                continue                       # kecamatan bernama sama di kabupaten lain
        elif not nama_wilayah_cocok(raw, kab):
            continue
        geo = raw.get("geojson") or {}
        if poligon is None and raw.get("class") == "boundary" and geo.get("type") in ("Polygon", "MultiPolygon"):
            poligon = raw
        if titik is None:
            titik = raw
    if titik is None:
        return None
    pusat = poligon or titik
    return {"lat": float(pusat["lat"]), "lon": float(pusat["lon"]),
            "geojson": poligon["geojson"] if poligon else None,
            "bbox": _bbox_raw(poligon) if poligon else None,
            "display_name": pusat.get("display_name", "")}


def dekat_kecamatan(lat: float, lon: float, kec_info) -> bool:
    """Hasil harus berada di (sekitar) kecamatan yang tertulis di LP."""
    if not kec_info:
        return True
    if kec_info.get("geojson"):
        return titik_dalam_wilayah(lat, lon, kec_info["geojson"], TOLERANSI_KEC_KM)
    return haversine_km(lat, lon, kec_info["lat"], kec_info["lon"]) <= RADIUS_KEC_KM


def nama_wilayah_cocok(raw: dict, nama_kab: str) -> bool:
    """Validasi cadangan (dipakai hanya bila poligon wilayah tidak tersedia):
    nama kabupaten/kota harus muncul di hierarki alamat hasil geocoding.
    Bagian pertama display_name (nama objek itu sendiri, misal 'Jalan Demak')
    sengaja diabaikan agar 'Jalan Demak' di Semarang tidak dikira Kab. Demak."""
    target = _nama_dasar(nama_kab)
    if not target:
        return False
    alamat = raw.get("address") or {}
    kunci_kab = ("county", "city", "municipality", "regency", "state_district")
    if any(k in alamat for k in kunci_kab):
        return any(_nama_dasar(alamat.get(k, "")) == target for k in kunci_kab)
    bagian = [b.strip() for b in str(raw.get("display_name", "")).split(",")][1:]
    return any(_nama_dasar(b) == target for b in bagian)


def susun_lapisan(info: dict) -> list[tuple[str, str, bool]]:
    """Urutan query (presisi, query, lokal) dari paling presisi ke paling kasar.

    - Kabupaten/kota SELALU ikut di query (anti-nyasar), tanpa kabupaten default.
    - Nama ditulis polos ("Cepu, Blora") karena itulah nama yang diindeks OSM.
    - lokal=True: query tanpa nama kecamatan (berguna bila data OSM tidak mencatat
      desa/jalan di bawah nama kecamatan itu) → pencarian dibatasi ke sekitar
      kecamatan TKP, dan hasilnya tetap wajib lolos uji jarak ke kecamatan.
    """
    poi, jl = info.get("poi", ""), info.get("jalan", "")
    dsn, ds = info.get("dusun", ""), info.get("desa", "")
    kc, kb = info.get("kecamatan", ""), info.get("kabupaten", "")
    calon = []
    if poi:
        calon.append((PRESISI_PATOKAN, [poi, kb], True))          # "Pasar Tempel, Grobogan"
    if jl and ds and kc:
        calon.append((PRESISI_JALAN, [jl, ds, kc, kb], False))
    if jl and kc:
        calon.append((PRESISI_JALAN, [jl, kc, kb], False))        # spesifikasi (a)
    if jl:
        calon.append((PRESISI_JALAN, [jl, kb], True))
    if dsn:
        calon.append((PRESISI_DUSUN, [dsn, ds, kb] if ds else [dsn, kb], True))
    if ds and kc:
        calon.append((PRESISI_DESA, [ds, kc, kb], False))
    if ds:
        calon.append((PRESISI_DESA, [ds, kb], True))
    if kc:
        calon.append((PRESISI_KEC, [kc, kb], False))              # spesifikasi (b)
    hasil, sudah = [], set()
    for presisi, bagian, lokal in calon:
        q = ", ".join(bagian)
        if q.lower() not in sudah:
            sudah.add(q.lower())
            hasil.append((presisi, q, lokal))
    return hasil


def _gagal(alasan: str, **lain) -> dict:
    return {"status": STATUS_GAGAL, "alasan": alasan, "lat": None, "lon": None,
            "presisi": "", "query": "", "validasi": "", "alamat_geocoder": "", **lain}


def geocode_berlapis(info: dict) -> dict:
    """Geocoding berlapis. Hasil hanya diterima bila titiknya (1) di dalam poligon
    kabupaten/kota TKP (atau, bila poligon tak tersedia, nama kab/kota cocok), dan
    (2) dekat kecamatan TKP bila kecamatannya ditemukan di peta."""
    kab, jenis = info.get("kabupaten", ""), info.get("jenis_wilayah", "")
    kec = info.get("kecamatan", "")
    if not kab:
        return _gagal("Kabupaten/Kota TKP tidak terbaca di LP")
    lapisan = susun_lapisan(info)
    if not lapisan:
        return _gagal("Jalan/desa/kecamatan TKP tidak terbaca di LP")
    label_wil = f"{jenis or 'Kab/Kota'} {kab}"
    try:
        wilayah = cari_wilayah(kab, jenis)
        kec_info = cari_kecamatan(kec, kab, jenis) if kec else None
        vb_kab = _perlebar(wilayah["bbox"], 0.02) if wilayah else None
        if kec_info and kec_info.get("bbox"):
            vb_lokal = _perlebar(kec_info["bbox"], 0.03)
        elif kec_info:
            vb_lokal = _perlebar((kec_info["lat"],) * 2 + (kec_info["lon"],) * 2, 0.11)
        else:
            vb_lokal = vb_kab
        cara_kab = (f"Titik di dalam batas {label_wil} (poligon OSM)" if wilayah
                    else f"Nama {label_wil} cocok di alamat (poligon tidak tersedia)")
        cara_kec = f" + dekat Kec. {kec}" if kec_info else ""

        dicoba = []
        for presisi, query, lokal in lapisan:
            dicoba.append(query)
            if presisi == PRESISI_KEC:                 # lapis (b): pusat kecamatan
                if kec_info:
                    return {"status": STATUS_OK, "alasan": "", "lat": kec_info["lat"],
                            "lon": kec_info["lon"], "presisi": presisi, "query": query,
                            "validasi": f"Pusat Kec. {kec} · {cara_kab}",
                            "alamat_geocoder": kec_info["display_name"]}
                continue
            kandidat = nominatim_cari(query, limit=5, viewbox=vb_lokal if lokal else vb_kab)
            if presisi in (PRESISI_DUSUN, PRESISI_DESA):   # utamakan objek pemukiman/wilayah
                kandidat = sorted(kandidat, key=lambda r: r.get("class") not in ("boundary", "place"))
            for raw in kandidat:
                lat, lon = float(raw["lat"]), float(raw["lon"])
                lolos = (titik_dalam_wilayah(lat, lon, wilayah["geojson"]) if wilayah
                         else nama_wilayah_cocok(raw, kab))
                if lolos and dekat_kecamatan(lat, lon, kec_info):
                    return {"status": STATUS_OK, "alasan": "", "lat": lat, "lon": lon,
                            "presisi": presisi, "query": query,
                            "validasi": f"{cara_kab}{cara_kec}",
                            "alamat_geocoder": raw.get("display_name", "")}
        return _gagal(f"Tidak ditemukan di dalam wilayah {label_wil}",
                      query=" | ".join(dicoba))
    except GeopyError as err:
        return _gagal(f"Gangguan koneksi geocoder ({type(err).__name__}) — coba 'Geocode ulang'")
    except Exception as err:          # data aneh tidak boleh menghentikan seluruh batch
        return _gagal(f"Error saat geocoding ({type(err).__name__}) — coba 'Geocode ulang'")


# =============================================================================
# 6. DATA LP (record, proses batch, impor/ekspor CSV)
# =============================================================================
def rekaman_baru(id_: str, nama_file: str) -> dict:
    return {
        "id": id_, "file": nama_file, "no_lp": "", "waktu": "", "polres": "",
        "tkp": "", "sumber_tkp": "", "jalan": "", "poi": "", "dusun": "", "desa": "", "kecamatan": "",
        "kabupaten": "", "jenis_wilayah": "", "sumber_wilayah": "", "patokan": "",
        "lat": None, "lon": None, "presisi": "", "status": STATUS_GAGAL,
        "alasan": "", "query": "", "validasi": "", "alamat_geocoder": "",
        "jenis_file": "", "selesai": False,
        "diproses": datetime.now(WIB).strftime("%Y-%m-%d %H:%M"),
    }


KOLOM = list(rekaman_baru("", "").keys())
EKSTENSI_DOKUMEN = ("pdf", "doc", "docx", "rtf")


def proses_satu_dokumen(id_: str, nama_file: str, isi: bytes) -> dict:
    rec = rekaman_baru(id_, nama_file)
    try:
        teks, jenis = ekstrak_teks(isi)
    except DokumenTidakTerbaca as err:
        rec["alasan"] = str(err)
        return rec
    except Exception as err:                       # file rusak / terenkripsi / tak terduga
        rec["alasan"] = f"File tidak bisa dibaca ({type(err).__name__})"
        return rec
    rec["jenis_file"] = jenis
    if len(teks.strip()) < 30:
        rec["alasan"] = ("PDF hasil scan/foto (tidak ada teks) — perlu OCR atau cek manual"
                         if jenis == "pdf" else "Dokumen kosong / hanya berisi gambar — cek manual")
        return rec
    rec.update(parse_lp(teks))
    rec.update(geocode_berlapis(rec))
    return rec


def pulihkan_rekaman(mentah: dict) -> dict | None:
    """Bentuk ulang rekaman dari CSV / penyimpanan HP dengan tipe data yang benar."""
    if not isinstance(mentah, dict) or not mentah.get("id"):
        return None
    rec = rekaman_baru(str(mentah["id"]), str(mentah.get("file") or ""))
    for k in KOLOM:
        if k in mentah and k not in ("lat", "lon", "selesai"):
            rec[k] = "" if mentah[k] is None else str(mentah[k])
    rec["lat"], rec["lon"] = _float_atau_none(mentah.get("lat")), _float_atau_none(mentah.get("lon"))
    if rec["lat"] is None or rec["lon"] is None:
        rec["lat"] = rec["lon"] = None
    rec["selesai"] = str(mentah.get("selesai")).strip().lower() in ("true", "1", "ya")
    return rec


def _float_atau_none(nilai):
    try:
        f = float(nilai)
        return None if math.isnan(f) else f
    except (TypeError, ValueError):
        return None


def impor_csv(isi: bytes) -> int:
    """Pulihkan hasil dari CSV yang pernah diunduh (tanpa upload ulang dokumen)."""
    df = pd.read_csv(io.BytesIO(isi), dtype=str, keep_default_na=False, encoding="utf-8-sig")
    if not {"id", "file", "lat", "lon", "status"}.issubset(df.columns):
        raise ValueError("Bukan CSV hasil aplikasi ini")
    data = st.session_state.data_lp
    jumlah = 0
    for baris in df.to_dict("records"):
        rec = pulihkan_rekaman(baris)
        if rec:
            data[rec["id"]] = rec
            jumlah += 1
    return jumlah


def ekspor_csv(data: dict) -> bytes:
    df = pd.DataFrame(list(data.values()), columns=KOLOM)
    return df.to_csv(index=False).encode("utf-8-sig")   # BOM → rapi dibuka di Excel


def ekspor_gpx(data: dict) -> bytes:
    """Titik TKP yang BELUM disurvei sebagai GPX — bisa diimpor ke aplikasi GPS
    lain yang punya alarm titik dan tetap berjalan di latar belakang."""
    e = html.escape
    wpt = [
        f'  <wpt lat="{t["lat"]:.6f}" lon="{t["lon"]:.6f}"><name>{e(t["lp"])}</name>'
        f'<desc>{e(t["tkp"])}</desc></wpt>'
        for t in titik_alarm(data)
    ]
    return ('<?xml version="1.0" encoding="UTF-8"?>\n'
            '<gpx version="1.1" creator="Survei TKP Laka" xmlns="http://www.topografix.com/GPX/1/1">\n'
            + "\n".join(wpt) + "\n</gpx>\n").encode("utf-8")


def antrekan_berkas(berkas: list) -> None:
    """CSV langsung dipulihkan; dokumen LP baru dimasukkan ke antrean proses."""
    data = st.session_state.data_lp
    for f in [b for b in berkas if b.name.lower().endswith(".csv")]:
        try:
            st.toast(f"📥 {impor_csv(f.getvalue())} data dipulihkan dari {f.name}")
        except Exception as err:
            st.error(f"CSV {f.name} gagal dibaca: {err}")

    antrian = st.session_state.antrian
    sudah = set(data) | {a[0] for a in antrian}
    id_baru = []
    for f in [b for b in berkas if b.name.lower().rsplit(".", 1)[-1] in EKSTENSI_DOKUMEN]:
        isi = f.getvalue()
        id_ = hashlib.md5(isi).hexdigest()       # file yang sama tidak diproses 2x
        if id_ not in sudah:
            antrian.append((id_, f.name, isi))
            sudah.add(id_)
            id_baru.append(id_)
    if not id_baru:
        st.toast("Tidak ada LP baru untuk diproses (semua sudah tersimpan).")
        return
    batch = st.session_state.batch or {"total": 0, "id": []}   # batch berjalan → digabung
    batch["total"] += len(id_baru)
    batch["id"] += id_baru
    st.session_state.batch = batch


def proses_antrian() -> None:
    """Proses antrean ±20 detik per putaran. Di akhir tiap putaran halaman
    dimuat ulang → hasil yang sudah jadi langsung tampil di peta & TERSIMPAN di
    HP. Bila koneksi putus di tengah jalan, hasil yang sudah jadi tidak hilang."""
    antrian, data = st.session_state.antrian, st.session_state.data_lp
    if not antrian:
        return
    total = max((st.session_state.batch or {}).get("total", 0), len(antrian))
    mulai, diproses = time.monotonic(), 0
    bar = st.progress(0.0, text="Memulai…")
    while antrian and (diproses == 0 or time.monotonic() - mulai < DETIK_PER_PUTARAN):
        diproses += 1
        id_, nama, isi = antrian[0]
        selesai = total - len(antrian)
        bar.progress(selesai / total, text=f"[{selesai + 1}/{total}] {_potong(nama, 40)}")
        data[id_] = proses_satu_dokumen(id_, nama, isi)
        antrian.pop(0)
    bar.empty()
    if not antrian:
        hasil = [data[i] for i in (st.session_state.batch or {}).get("id", []) if i in data]
        ok = sum(r["lat"] is not None for r in hasil)
        st.session_state.batch = {}
        st.session_state.pesan_batch = (f"Selesai: {len(hasil)} LP diproses · ✅ {ok} terpetakan · "
                                        f"⚠️ {len(hasil) - ok} perlu cek manual · 💾 tersimpan di HP")


def geocode_ulang_yang_gagal() -> None:
    """Ulangi geocoding (tanpa dokumen) untuk LP gagal yang kabupatennya terbaca."""
    data = st.session_state.data_lp
    target = [r for r in data.values()
              if r["lat"] is None and r["status"] == STATUS_GAGAL and r.get("kabupaten")]
    if not target:
        st.toast("Tidak ada LP gagal yang bisa diulang.")
        return
    bar = st.progress(0.0, text="Geocode ulang…")
    for i, r in enumerate(target, start=1):
        bar.progress((i - 1) / len(target), text=f"[{i}/{len(target)}] {_potong(r['file'], 40)}")
        r.update(geocode_berlapis(r))
    bar.empty()


# =============================================================================
# 7. URL GOOGLE MAPS
# =============================================================================
def url_navigasi(lat: float, lon: float) -> str:
    """Di Android, link ini otomatis membuka aplikasi Google Maps (mode rute
    dari posisi Anda saat ini ke TKP)."""
    return f"https://www.google.com/maps/dir/?api=1&destination={lat:.6f},{lon:.6f}"


def url_cari(teks: str) -> str:
    return "https://www.google.com/maps/search/?api=1&query=" + urllib.parse.quote(teks)


def teks_cari_google(r: dict) -> str:
    """Kata kunci pencarian Google Maps dari patokan + dusun + desa + kec + kab.
    Google Maps biasanya jauh lebih kenal patokan lokal (pasar, warung, SD)."""
    bagian = [r.get("poi"), r.get("dusun") and f"Dusun {r['dusun']}",
              r.get("desa"), r.get("kecamatan"), r.get("kabupaten")]
    teks = ", ".join(b for b in bagian if b)
    return teks if (r.get("poi") or r.get("dusun") or r.get("desa")) else (r.get("tkp") or teks)


# =============================================================================
# 8. PETA FOLIUM
# =============================================================================
def _html_popup(r: dict) -> str:
    e = html.escape
    nav = e(url_navigasi(r["lat"], r["lon"]))
    return (
        "<div style='font-family:sans-serif;font-size:13px;min-width:190px'>"
        f"<b>{e(_potong(r.get('no_lp') or r['file'], 70))}</b><br>"
        f"{e(_potong(r.get('tkp', ''), 130))}<br>"
        f"<span style='color:#666'>Presisi: {e(r.get('presisi', ''))}</span><br>"
        + ("<span style='color:#b45309'>⚠️ Perkiraan — bukan titik TKP persis</span><br>"
           if r.get("presisi") in PRESISI_KASAR else "")
        + ("<span style='color:#15803d'>✅ Sudah disurvei</span><br>" if r.get("selesai") else "")
        + f"<a href='{nav}' target='_blank' rel='noopener' style='display:inline-block;"
        "margin-top:6px;padding:7px 12px;background:#1a73e8;color:#fff;border-radius:6px;"
        "text-decoration:none;font-weight:600'>🧭 Navigasi</a></div>"
    )


def buat_peta(titik: list[dict], gps: dict | None, radius_km: float,
              id_dalam_radius: set) -> folium.Map:
    m = folium.Map(location=[-2.5, 118.0], zoom_start=5, tiles=None,
                   control_scale=True, max_zoom=21)

    # --- Basemap: Google Maps (default), Google Satelit, OpenStreetMap
    folium.TileLayer(tiles=TILE_GOOGLE_JALAN, attr="Peta © Google", name="Google Maps",
                     subdomains="0123", max_zoom=21).add_to(m)
    folium.TileLayer(tiles=TILE_GOOGLE_HYBRID, attr="Citra © Google", name="Google Satelit",
                     subdomains="0123", max_zoom=21, show=False).add_to(m)
    folium.TileLayer("OpenStreetMap", name="OpenStreetMap", show=False).add_to(m)

    Fullscreen(position="topleft", title="Layar penuh", title_cancel="Keluar layar penuh").add_to(m)
    # Titik biru "live" di dalam peta (ikut bergerak saat Anda berjalan).
    LocateControl(auto_start=False, keepCurrentZoomLevel=True, flyTo=True,
                  strings={"title": "Tampilkan posisi saya (live)"},
                  locateOptions={"enableHighAccuracy": True}).add_to(m)

    # --- Lingkaran radius survei di sekitar GPS
    if gps:
        lat0, lon0 = gps["lat"], gps["lon"]
        folium.Circle(location=[lat0, lon0], radius=radius_km * 1000, color="#1a73e8",
                      weight=2, fill=True, fill_color="#1a73e8", fill_opacity=0.08,
                      tooltip=f"Radius survei {radius_km} km").add_to(m)
        if gps.get("akurasi"):
            folium.Circle(location=[lat0, lon0], radius=gps["akurasi"], color="#1a73e8",
                          weight=0, fill=True, fill_opacity=0.18).add_to(m)
        folium.Marker([lat0, lon0], tooltip=f"📍 Posisi saya ({gps['sumber']})",
                      icon=folium.Icon(color="blue", icon="user", prefix="fa")).add_to(m)
        dlat = radius_km / 110.574
        dlon = radius_km / (111.320 * math.cos(math.radians(lat0)))
        m.fit_bounds([[lat0 - dlat, lon0 - dlon], [lat0 + dlat, lon0 + dlon]])
    elif titik:
        lats, lons = [r["lat"] for r in titik], [r["lon"] for r in titik]
        m.fit_bounds([[min(lats), min(lons)], [max(lats), max(lons)]], max_zoom=15)

    # --- Marker TKP dikelompokkan dengan MarkerCluster
    # Tanpa disableClusteringAtZoom: LP yang jatuh di titik SAMA tetap jadi cluster
    # dan "dipencarkan" (spiderfy) saat diketuk, tidak saling menutupi.
    cluster = MarkerCluster(name="TKP laka", maxClusterRadius=45,
                            spiderfyOnMaxZoom=True, showCoverageOnHover=False).add_to(m)
    for r in titik:
        dalam = gps is None or r["id"] in id_dalam_radius
        warna = WARNA_MARKER.get(r.get("presisi"), "red") if dalam else "lightgray"
        ikon = "crosshairs" if r.get("presisi") in (PRESISI_KEC, PRESISI_KEC_LAMA) else "car"
        if r.get("selesai"):
            warna, ikon = ("green" if dalam else "lightgray"), "check"
        folium.Marker(
            [r["lat"], r["lon"]],
            popup=folium.Popup(_html_popup(r), max_width=280),
            tooltip=html.escape(_potong(r.get("no_lp") or r["file"], 50)),
            icon=folium.Icon(color=warna, icon=ikon, prefix="fa"),
        ).add_to(cluster)

    folium.LayerControl(collapsed=True).add_to(m)
    return m


def sidik_peta(titik: list[dict], gps: dict | None, radius_km: float) -> str:
    """Key komponen peta. streamlit-folium hanya menggambar peta SEKALI per key,
    jadi key harus berubah saat GPS/radius/data berubah agar peta ikut ter-update
    (dan tetap sama bila tidak ada perubahan → peta tidak berkedip)."""
    bahan = [round(gps["lat"], 5), round(gps["lon"], 5), gps.get("akurasi")] if gps else []
    bahan += [radius_km] + [(r["id"], round(r["lat"], 6), round(r["lon"], 6), r.get("presisi"),
                             r.get("no_lp"), r.get("tkp"), bool(r.get("selesai"))) for r in titik]
    return hashlib.md5(repr(bahan).encode()).hexdigest()[:12]


# =============================================================================
# 9. KOMPONEN PONSEL: PENYIMPANAN DI HP + ALARM KEDEKATAN TKP (JavaScript)
# -----------------------------------------------------------------------------
# Berjalan DI BROWSER HP, bukan di server:
#  • Penyimpanan: data LP disimpan di localStorage browser HP. Saat aplikasi
#    dibuka lagi, data dimuat kembali → tidak perlu upload ulang. Server
#    Streamlit Cloud tidak menyimpan apa pun (servernya juga di-reset berkala).
#  • Alarm: GPS dipantau terus (watchPosition). Saat jarak ke TKP ≤ radius
#    (default 500 m) → HP bergetar, berbunyi, menyebut TKP, dan tampil banner
#    berisi tombol Navigasi. Perhitungan jarak dilakukan di HP (tanpa internet
#    tambahan, tanpa memuat ulang halaman).
#  Batasan browser: alarm hanya berjalan selama halaman aplikasi terbuka &
#  layar menyala (browser menghentikan halaman yang di latar belakang).
# =============================================================================
KUNCI_PENYIMPANAN = "jr_tkp_data_v1"

HTML_KOMPONEN_PONSEL = r"""<!doctype html>
<html lang="id"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<style>
  :root { --teks:#1f2937; --redup:#4b5563; --latar:#ffffff; --latar2:#f3f4f6;
          --utama:#1a73e8; --bahaya:#d93025; --garis:#d9dce1; }
  html, body { margin:0; padding:0; background:transparent; color:var(--teks);
               font-family:"Source Sans Pro", system-ui, -apple-system, sans-serif; font-size:15px; }
  .kartu { border:1px solid var(--garis); border-radius:14px; padding:10px 12px; background:var(--latar); }
  .baris { display:flex; gap:8px; align-items:center; }
  button, select { font:inherit; min-height:46px; border-radius:10px; border:1px solid var(--garis);
                   background:var(--latar2); color:var(--teks); padding:0 12px; font-weight:600; }
  #tombol { flex:1; background:var(--utama); border-color:var(--utama); color:#fff; }
  #tombol.aktif { background:var(--latar); color:var(--bahaya); border-color:var(--bahaya); }
  .status { font-size:13.5px; color:var(--redup); margin-top:7px; line-height:1.35; }
  .catatan { font-size:12px; color:#92400e; margin-top:3px; line-height:1.3; }
  .banner { display:none; margin-top:10px; border-radius:12px; background:#fde8e7;
            border:2px solid var(--bahaya); padding:10px; color:#3c0a07; }
  .banner.tampil { display:block; animation:kedip .8s ease-in-out 4; }
  @keyframes kedip { 50% { background:#f9b9b3; } }
  .banner .judul { font-weight:700; color:var(--bahaya); font-size:18px; }
  .banner .lp { font-weight:600; margin-top:3px; word-break:break-word; }
  .banner .tkp { font-size:14px; margin-top:2px; }
  .banner .baris { margin-top:8px; }
  .banner a { flex:1; display:flex; align-items:center; justify-content:center; min-height:46px;
              border-radius:10px; background:var(--utama); color:#fff; text-decoration:none; font-weight:700; }
  .simpan { font-size:12.5px; color:var(--redup); margin-top:8px; border-top:1px dashed var(--garis); padding-top:6px; }
</style></head>
<body>
<div class="kartu">
  <div class="baris">
    <button id="tombol" type="button">🔔 Aktifkan Alarm TKP</button>
    <select id="radius" aria-label="Radius alarm">
      <option value="200">200 m</option><option value="300">300 m</option>
      <option value="500" selected>500 m</option><option value="1000">1 km</option>
    </select>
  </div>
  <div id="status" class="status">Alarm mati. Aktifkan agar HP berbunyi &amp; bergetar saat Anda melintas dekat TKP.</div>
  <div id="catatan" class="catatan"></div>
  <div id="banner" class="banner" role="alert" aria-live="assertive">
    <div class="judul" id="b-judul"></div>
    <div class="lp" id="b-lp"></div>
    <div class="tkp" id="b-tkp"></div>
    <div class="baris"><a id="b-nav" target="_blank" rel="noopener">🧭 Navigasi ke TKP</a>
      <button id="b-tutup" type="button">Tutup</button></div>
  </div>
  <div id="simpan" class="simpan">⏳ Memuat data LP tersimpan di HP…</div>
</div>
<script>
(function () {
  "use strict";
  var KUNCI_DATA = "__KUNCI__", KUNCI_RADIUS = "jr_tkp_alarm_radius";
  var BATAS_AKURASI = 250;          // fix GPS lebih kasar dari ini diabaikan (meter)
  var titik = [], sesiDijawab = null, nilaiBesar = false, versiTersimpan = null, nTersimpan = 0;
  var aktif = false, idWatch = null, idCadangan = null, waktuFix = 0;
  var audio = null, wakeLock = null, dalam = {}, idBanner = null, posTerakhir = null;
  var $ = function (id) { return document.getElementById(id); };

  // ---------- protokol komponen Streamlit (tanpa library) ----------
  function kirim(tipe, data) {
    var p = { isStreamlitMessage: true, type: tipe };
    for (var k in data) { p[k] = data[k]; }
    window.parent.postMessage(p, "*");
  }
  function aturTinggi() {
    kirim("streamlit:setFrameHeight", { height: Math.ceil(document.body.scrollHeight) + 4 });
  }

  // ---------- penyimpanan di HP (localStorage) ----------
  function bacaLS(k) { try { return window.localStorage.getItem(k); } catch (e) { return undefined; } }
  function tulisLS(k, v) { try { window.localStorage.setItem(k, v); return true; } catch (e) { return e; } }
  function jam(iso) {
    try { var d = new Date(iso); return ("0" + d.getHours()).slice(-2) + ":" + ("0" + d.getMinutes()).slice(-2); }
    catch (e) { return ""; }
  }
  function muatData() {
    var s = bacaLS(KUNCI_DATA);
    if (s === undefined) { return { aksi: "muat", ok: false, data: [], pesan: "Penyimpanan browser tidak tersedia (mode penyamaran?)" }; }
    if (!s) { return { aksi: "muat", ok: true, data: [] }; }
    try {
      var o = JSON.parse(s);
      return { aksi: "muat", ok: true, data: Array.isArray(o.data) ? o.data : [], waktu: o.waktu || null };
    } catch (e) { return { aksi: "muat", ok: false, data: [], pesan: "Data tersimpan rusak" }; }
  }
  function statusSimpan(t) { $("simpan").textContent = t; }

  // ---------- util jarak ----------
  function jarak(a, b, c, d) {
    var r = Math.PI / 180, dp = (c - a) * r, dl = (d - b) * r;
    var x = Math.sin(dp / 2) * Math.sin(dp / 2) + Math.cos(a * r) * Math.cos(c * r) * Math.sin(dl / 2) * Math.sin(dl / 2);
    return 2 * 6371008.8 * Math.asin(Math.sqrt(x));
  }
  function fmt(m) { return m < 1000 ? (Math.round(m / 10) * 10) + " m" : (m / 1000).toFixed(1).replace(".", ",") + " km"; }
  function radius() { return parseInt($("radius").value, 10) || 500; }

  // ---------- efek alarm ----------
  function bip() {
    if (!audio) { return; }
    try {
      var t0 = audio.currentTime + 0.05;
      for (var k = 0; k < 3; k++) {
        var o = audio.createOscillator(), g = audio.createGain();
        o.type = "square"; o.frequency.value = 880; g.gain.value = 0.25;
        o.connect(g); g.connect(audio.destination);
        o.start(t0 + k * 0.35); o.stop(t0 + k * 0.35 + 0.2);
      }
    } catch (e) {}
  }
  function ucap(teks) {
    try {
      if (!window.speechSynthesis) { return; }
      window.speechSynthesis.cancel();
      var u = new SpeechSynthesisUtterance(teks);
      u.lang = "id-ID";
      window.speechSynthesis.speak(u);
    } catch (e) {}
  }
  function getar(pola) { try { if (navigator.vibrate) { navigator.vibrate(pola); } } catch (e) {} }

  function tampilBanner(t, lainnya) {
    idBanner = t.id;
    $("b-judul").textContent = "🚨 TKP dekat · " + fmt(t._d);
    $("b-lp").textContent = t.lp;
    $("b-tkp").textContent = t.tkp + (t.perkiraan ? " (titik perkiraan)" : "") +
      (lainnya > 0 ? " · +" + lainnya + " TKP lain dalam radius" : "");
    $("b-nav").href = t.nav;
    var b = $("banner");
    b.classList.remove("tampil"); void b.offsetWidth; b.classList.add("tampil");
    aturTinggi();
  }
  function sembunyiBanner() { idBanner = null; $("banner").classList.remove("tampil"); aturTinggi(); }
  function bunyikan(t, lainnya) {
    tampilBanner(t, lainnya);
    getar([500, 200, 500, 200, 500]);
    bip();
    ucap("Perhatian. TKP dekat, sekitar " + (Math.round(t._d / 10) * 10) + " meter. " + (t.suara || ""));
  }

  // ---------- evaluasi posisi ----------
  function evaluasi(pos) {
    posTerakhir = pos; waktuFix = Date.now();
    var lat = pos.coords.latitude, lon = pos.coords.longitude, akurasi = pos.coords.accuracy || 0;
    if (akurasi > BATAS_AKURASI) {
      $("status").textContent = "📡 Akurasi GPS rendah (±" + Math.round(akurasi) + " m) — menunggu sinyal lebih baik…";
      aturTinggi(); return;
    }
    var R = radius(), terdekat = null, baru = [], nDalam = 0, ada = {};
    for (var i = 0; i < titik.length; i++) {
      var t = titik[i]; ada[t.id] = t;
      t._d = jarak(lat, lon, t.lat, t.lon);
      if (!terdekat || t._d < terdekat._d) { terdekat = t; }
      if (t._d <= R) { nDalam++; if (!dalam[t.id]) { dalam[t.id] = true; baru.push(t); } }
      else if (t._d > R * 1.3 + 50) { dalam[t.id] = false; }      // re-arm setelah benar-benar menjauh
    }
    if (baru.length) {
      baru.sort(function (a, b) { return a._d - b._d; });
      bunyikan(baru[0], nDalam - 1);
    } else if (idBanner) {
      var tb = ada[idBanner];
      if (!tb || tb._d > R * 1.3 + 50) { sembunyiBanner(); }
      else { $("b-judul").textContent = "🚨 TKP dekat · " + fmt(tb._d); }
    }
    var s = "📡 GPS aktif ±" + Math.round(akurasi) + " m";
    if (!titik.length) { s += " · belum ada TKP terpetakan"; }
    else if (terdekat) { s += " · TKP terdekat " + fmt(terdekat._d) + " (" + terdekat.lp + ")"; }
    if (nDalam) { s += " · 🎯 " + nDalam + " TKP dalam " + fmt(R); }
    $("status").textContent = s;
    aturTinggi();
  }
  function galatGps(err) {
    if (err && err.code === 1) {
      $("status").textContent = "⛔ Izin lokasi ditolak. Di Chrome: ⋮ → Setelan → Setelan situs → Lokasi → izinkan situs ini, lalu aktifkan lagi.";
      matikan(false);
    } else if (err && err.code === 2) {
      $("status").textContent = "📡 Lokasi tidak tersedia — pastikan GPS/Lokasi HP menyala. Mencoba lagi…";
    } else {
      $("status").textContent = "📡 Menunggu sinyal GPS…";
    }
    aturTinggi();
  }

  // ---------- layar tetap menyala ----------
  function mintaWakeLock() {
    if (!("wakeLock" in navigator)) {
      $("catatan").textContent = "⚠️ Alarm berhenti saat layar mati. Perpanjang 'Waktu tunggu layar' di Setelan HP.";
      aturTinggi(); return;
    }
    navigator.wakeLock.request("screen").then(function (w) {
      wakeLock = w;
      $("catatan").textContent = "🔆 Layar dijaga tetap menyala. Biarkan aplikasi ini terbuka di layar selama perjalanan.";
      w.addEventListener("release", function () { wakeLock = null; });
      aturTinggi();
    }).catch(function () {
      $("catatan").textContent = "⚠️ Layar bisa mati otomatis & alarm ikut berhenti. Perpanjang 'Waktu tunggu layar' di Setelan HP.";
      aturTinggi();
    });
  }
  document.addEventListener("visibilitychange", function () {
    if (aktif && document.visibilityState === "visible" && !wakeLock) { mintaWakeLock(); }
  });

  // ---------- nyala / mati ----------
  function nyalakan() {
    if (!("geolocation" in navigator)) { $("status").textContent = "⛔ Browser ini tidak mendukung GPS."; return; }
    try {                                 // harus dipicu ketukan: membuka izin suara
      var AC = window.AudioContext || window.webkitAudioContext;
      if (AC && !audio) { audio = new AC(); }
      if (audio && audio.state === "suspended") { audio.resume(); }
    } catch (e) {}
    getar(80);
    ucap("Alarm TKP aktif");
    mintaWakeLock();
    dalam = {};                           // TKP yang sudah dekat saat ini langsung diumumkan
    idWatch = navigator.geolocation.watchPosition(evaluasi, galatGps,
      { enableHighAccuracy: true, maximumAge: 5000, timeout: 30000 });
    // Cadangan: beberapa HP berhenti mengirim posisi → minta manual tiap 20 detik.
    idCadangan = setInterval(function () {
      if (aktif && Date.now() - waktuFix > 25000) {
        navigator.geolocation.getCurrentPosition(evaluasi, galatGps,
          { enableHighAccuracy: true, maximumAge: 10000, timeout: 20000 });
      }
    }, 20000);
    aktif = true; waktuFix = Date.now();
    $("tombol").textContent = "🔕 Matikan Alarm"; $("tombol").classList.add("aktif");
    $("status").textContent = "📡 Mencari sinyal GPS…";
    aturTinggi();
  }
  function matikan(ubahStatus) {
    if (idWatch !== null) { navigator.geolocation.clearWatch(idWatch); idWatch = null; }
    if (idCadangan !== null) { clearInterval(idCadangan); idCadangan = null; }
    if (wakeLock) { try { wakeLock.release(); } catch (e) {} wakeLock = null; }
    aktif = false; sembunyiBanner();
    $("tombol").textContent = "🔔 Aktifkan Alarm TKP"; $("tombol").classList.remove("aktif");
    $("catatan").textContent = "";
    if (ubahStatus !== false) { $("status").textContent = "Alarm mati."; }
    aturTinggi();
  }
  $("tombol").addEventListener("click", function () { if (aktif) { matikan(); } else { nyalakan(); } });
  $("b-tutup").addEventListener("click", sembunyiBanner);
  var rTersimpan = bacaLS(KUNCI_RADIUS);
  if (rTersimpan && $("radius").querySelector('option[value="' + rTersimpan + '"]')) { $("radius").value = rTersimpan; }
  $("radius").addEventListener("change", function () {
    tulisLS(KUNCI_RADIUS, $("radius").value);
    dalam = {};
    if (aktif && posTerakhir) { evaluasi(posTerakhir); }
  });

  // ---------- data dari Python ----------
  function terapkanTema(tema) {
    if (!tema) { return; }
    var s = document.documentElement.style;
    if (tema.textColor) { s.setProperty("--teks", tema.textColor); s.setProperty("--redup", tema.textColor); }
    if (tema.backgroundColor) { s.setProperty("--latar", tema.backgroundColor); }
    if (tema.secondaryBackgroundColor) { s.setProperty("--latar2", tema.secondaryBackgroundColor); }
  }
  function onRender(args, tema) {
    terapkanTema(tema);
    var sesi = args.sesi || "";
    // Jabat tangan per SESI server: data tersimpan dikirim ke Python sekali untuk
    // tiap sesi baru (termasuk saat koneksi HP tersambung ulang ke sesi baru).
    if (sesi && !args.dimuat && sesi !== sesiDijawab) {
      sesiDijawab = sesi;
      var hasil = muatData();
      hasil.sesi = sesi;
      nilaiBesar = hasil.data.length > 0;
      statusSimpan(hasil.ok ? (hasil.data.length ? "📂 " + hasil.data.length + " LP tersimpan ditemukan — memuat…"
                                                 : "💾 Belum ada LP tersimpan di HP ini.")
                            : "⚠️ " + hasil.pesan + " — data tidak bisa disimpan di HP ini.");
      kirim("streamlit:setComponentValue", { value: hasil, dataType: "json" });
    } else if (args.dimuat && nilaiBesar) {
      // Python sudah menerima data → ganti nilai komponen dengan yang kecil.
      // (Nilai komponen ikut terkirim ke server di SETIAP ketukan; jangan biarkan besar.)
      nilaiBesar = false;
      kirim("streamlit:setComponentValue", { value: { aksi: "siap", sesi: sesi }, dataType: "json" });
    }
    if (args.dimuat === true && typeof args.data === "string" && args.versi && args.versi !== versiTersimpan) {
      var waktu = new Date().toISOString();
      var r = tulisLS(KUNCI_DATA, '{"v":1,"waktu":"' + waktu + '","data":' + args.data + "}");
      if (r === true) {
        versiTersimpan = args.versi; nTersimpan = args.n || 0;
        statusSimpan(nTersimpan ? "💾 " + nTersimpan + " LP tersimpan di HP ini · diperbarui " + jam(waktu)
                                : "💾 Belum ada LP tersimpan di HP ini.");
      } else {
        statusSimpan("⚠️ Gagal menyimpan di HP (" + ((r && r.name === "QuotaExceededError") ?
          "memori browser penuh" : String(r)) + ") — unduh CSV sebagai cadangan.");
      }
    }
    titik = Array.isArray(args.titik) ? args.titik : [];
    if (aktif && posTerakhir) { evaluasi(posTerakhir); }
    aturTinggi();
  }
  window.addEventListener("message", function (ev) {
    var d = ev.data;
    if (ev.source !== window.parent || !d || d.type !== "streamlit:render") { return; }
    onRender(d.args || {}, d.theme || null);
  });
  if (window.ResizeObserver) { new ResizeObserver(aturTinggi).observe(document.body); }
  kirim("streamlit:componentReady", { apiVersion: 1 });
})();
</script>
</body></html>
""".replace("__KUNCI__", KUNCI_PENYIMPANAN)


def _siapkan_komponen_ponsel():
    """Tulis index.html komponen ke folder sementara lalu daftarkan ke Streamlit.
    Dengan cara ini aplikasi tetap SATU file app.py (tidak perlu folder tambahan)."""
    # Versi = sidik isi HTML → setiap kali kode komponen berubah, alamatnya ikut
    # berubah sehingga HP tidak memakai salinan lama dari cache browser.
    versi = hashlib.md5(HTML_KOMPONEN_PONSEL.encode("utf-8")).hexdigest()[:8]
    folder = os.path.realpath(os.path.join(tempfile.gettempdir(), f"jr_tkp_ponsel_{versi}"))
    os.makedirs(folder, exist_ok=True)
    berkas = os.path.join(folder, "index.html")
    try:
        with open(berkas, encoding="utf-8") as f:
            sama = f.read() == HTML_KOMPONEN_PONSEL
    except OSError:
        sama = False
    if not sama:
        sementara = f"{berkas}.{os.getpid()}.tmp"
        with open(sementara, "w", encoding="utf-8") as f:
            f.write(HTML_KOMPONEN_PONSEL)
        os.replace(sementara, berkas)
    return components.declare_component(f"tkp_ponsel_{versi}", path=folder)


_komponen_ponsel = _siapkan_komponen_ponsel()


def titik_alarm(data: dict) -> list[dict]:
    """TKP yang ikut alarm: punya koordinat, belum disurvei, dan bukan sekadar
    'pusat kecamatan' (terlalu kasar — alarmnya akan menyesatkan)."""
    hasil = []
    for r in data.values():
        if r.get("lat") is None or r.get("lon") is None or r.get("selesai"):
            continue
        if r.get("presisi") in (PRESISI_KEC, PRESISI_KEC_LAMA):
            continue
        hasil.append({
            "id": r["id"], "lat": round(r["lat"], 6), "lon": round(r["lon"], 6),
            "lp": _potong(r.get("no_lp") or r["file"], 70),
            "tkp": _potong(r.get("tkp") or r.get("jalan") or "", 140),
            "suara": _potong(r.get("poi") or r.get("jalan") or r.get("desa") or "", 60),
            "nav": url_navigasi(r["lat"], r["lon"]),
            "perkiraan": r.get("presisi") in PRESISI_KASAR,
        })
    return hasil


def sinkron_ponsel() -> None:
    """Muat data tersimpan di HP (sekali per sesi) & simpan setiap perubahan.
    Selama data HP belum termuat, aplikasi TIDAK menyimpan apa pun — supaya data
    lama di HP tidak tertimpa data kosong.

    'sesi' = penanda unik sesi server ini. Bila server membuat sesi baru (mis.
    HP tersambung ulang setelah layar mati lama), penandanya berubah sehingga HP
    otomatis mengirim ulang data tersimpannya."""
    data = st.session_state.data_lp
    sesi = st.session_state.setdefault("_hp_sesi", secrets.token_hex(6))
    dimuat = st.session_state.get("_hp_dimuat", False)
    payload = versi = None
    if dimuat:
        # Teks JSON yang sama → pesan sama → Streamlit hanya mengirim rujukan cache
        # (bukan ratusan KB) ke HP selama data tidak berubah.
        payload = json.dumps(list(data.values()), ensure_ascii=False, separators=(",", ":"))
        versi = hashlib.md5(payload.encode("utf-8")).hexdigest()
    nilai = _komponen_ponsel(key="tkp_ponsel", default=None, sesi=sesi, dimuat=dimuat,
                             data=payload, versi=versi, n=len(data), titik=titik_alarm(data))
    if (not dimuat and isinstance(nilai, dict) and nilai.get("aksi") == "muat"
            and nilai.get("sesi") == sesi):
        st.session_state._hp_dimuat = True
        tambah = 0
        for mentah in nilai.get("data") or []:
            rec = pulihkan_rekaman(mentah)
            if rec and rec["id"] not in data:
                data[rec["id"]] = rec
                tambah += 1
        if tambah:   # ditampilkan di putaran berikutnya (toast hilang bila langsung rerun)
            st.session_state.pesan_toast = f"📂 {tambah} LP tersimpan di HP dimuat kembali"
        st.rerun()


# =============================================================================
# 10. KOMPONEN UI
# =============================================================================
CSS_MOBILE = """
<style>
  .block-container {padding: 0.8rem 0.75rem 4rem 0.75rem; max-width: 820px;}
  [data-testid="stDecoration"], footer {display: none !important;}
  h3 {margin: 0 0 0.2rem 0 !important; padding: 0 !important;}
  /* Tombol besar, mudah diketuk jempol */
  [data-testid="stLinkButton"] a, [data-testid="stButton"] button,
  [data-testid="stFormSubmitButton"] button, [data-testid="stDownloadButton"] button {
      min-height: 48px; font-size: 1rem; font-weight: 600;
  }
  [data-testid="stVerticalBlockBorderWrapper"] {border-radius: 14px;}
</style>
"""


def cek_akses() -> bool:
    """Gerbang kata sandi sederhana (aktif bila APP_PASSWORD diisi di Secrets)."""
    sandi = _secret("APP_PASSWORD")
    if not sandi or st.session_state.get("akses_ok"):
        return True
    st.markdown("### 🔒 Survei TKP")
    with st.form("form_login"):
        isian = st.text_input("Kata sandi aplikasi", type="password")
        if st.form_submit_button("Masuk", type="primary", width="stretch"):
            if hmac.compare_digest(isian.encode(), sandi.encode()):
                st.session_state.akses_ok = True
                st.rerun()
            st.error("Kata sandi salah.")
    return False


def _serap_gps(nilai) -> None:
    """Simpan posisi dari komponen GPS. Hanya fix BARU yang menimpa posisi,
    sehingga lokasi manual tidak tertimpa nilai GPS lama saat rerun."""
    if not isinstance(nilai, dict) or nilai.get("latitude") is None or nilai.get("longitude") is None:
        return
    sidik = (nilai["latitude"], nilai["longitude"], nilai.get("accuracy"))
    if st.session_state.get("_gps_sidik") == sidik:
        return
    st.session_state._gps_sidik = sidik
    st.session_state.gps = {
        "lat": float(nilai["latitude"]), "lon": float(nilai["longitude"]),
        "akurasi": float(nilai["accuracy"]) if nilai.get("accuracy") else None,
        "sumber": "GPS HP", "waktu": datetime.now(WIB).strftime("%H:%M WIB"),
    }


def panel_lokasi() -> tuple[dict | None, int]:
    with st.container(border=True):
        kol_tombol, kol_info = st.columns([1, 5], vertical_alignment="center")
        with kol_tombol:
            # Komponen ini memakai key internal "loc" — jangan pakai key itu di tempat lain.
            nilai = streamlit_geolocation()
        _serap_gps(nilai)
        gps = st.session_state.gps
        with kol_info:
            if gps:
                teks = f"**📍 {gps['sumber']}** · `{gps['lat']:.5f}, {gps['lon']:.5f}`"
                if gps.get("akurasi"):
                    teks += f" · ±{gps['akurasi']:.0f} m"
                st.markdown(teks + f" · {gps['waktu']}")
                if gps.get("akurasi") and gps["akurasi"] > 1000:
                    st.caption("⚠️ Akurasi rendah — aktifkan GPS/‘Akurasi tinggi’ di HP lalu ketuk lagi.")
            else:
                st.markdown("Ketuk tombol 📍 untuk mengambil lokasi GPS HP Anda.")
        radius = st.slider("🎯 Radius survei (km)", min_value=RADIUS_MIN_KM,
                           max_value=RADIUS_MAX_KM, value=RADIUS_DEFAULT_KM, step=1,
                           key="radius_km")
        with st.expander("⌨️ Lokasi manual (jika GPS tidak merespons)"):
            isian = st.text_input("Koordinat atau link Google Maps",
                                  placeholder="-6.89412, 110.63785", key="isian_lokasi_manual")
            if st.button("Pakai lokasi ini", key="btn_lokasi_manual", width="stretch"):
                k = parse_koordinat(isian)
                if k:
                    st.session_state.gps = {"lat": k[0], "lon": k[1], "akurasi": None,
                                            "sumber": "Manual",
                                            "waktu": datetime.now(WIB).strftime("%H:%M WIB")}
                    st.rerun()
                st.error("Format tidak dikenali. Contoh: -6.89412, 110.63785")
            if gps and st.button("Hapus lokasi", key="btn_hapus_lokasi", width="stretch"):
                st.session_state.gps = None
                st.rerun()
    return st.session_state.gps, radius


def panel_upload() -> None:
    data = st.session_state.data_lp
    with st.expander("📂 Upload & proses LP", expanded=not data or bool(st.session_state.antrian)):
        berkas = st.file_uploader(
            "LP format PDF / Word (.doc, .docx) — bisa banyak sekaligus — atau CSV hasil sebelumnya",
            type=["pdf", "doc", "docx", "rtf", "csv"], accept_multiple_files=True, key="uploader",
        )
        if st.button(f"⚙️ Proses {len(berkas or [])} file", type="primary",
                     width="stretch", disabled=not berkas, key="btn_proses"):
            antrekan_berkas(berkas)
        if st.session_state.antrian:
            proses_antrian()
            if st.button("⏹️ Hentikan proses", width="stretch", key="btn_henti"):
                st.session_state.antrian = []
                st.session_state.batch = {}
                st.rerun()
        if st.session_state.get("pesan_batch"):
            st.success(st.session_state.pop("pesan_batch"))
        st.caption("Geocoding mengikuti batas Nominatim (±1 detik/permintaan). Ratusan LP butuh "
                   "beberapa menit — biarkan layar menyala. Hasil disimpan ke HP setiap ±20 detik; "
                   "bila terhenti, upload lagi & tekan Proses: LP yang sudah jadi otomatis dilewati.")
        if data:
            st.download_button("⬇️ Unduh hasil (CSV)", data=ekspor_csv(data),
                               file_name=f"hasil_tkp_{datetime.now(WIB):%Y%m%d_%H%M}.csv",
                               mime="text/csv", width="stretch", key="btn_unduh")
            st.caption("Data otomatis tersimpan di HP ini. Untuk memindahkan ke HP lain / rekan "
                       "tim: unduh CSV, lalu upload CSV-nya di HP tersebut.")
            st.download_button("🗺️ Unduh titik TKP belum disurvei (GPX)", data=ekspor_gpx(data),
                               file_name=f"tkp_{datetime.now(WIB):%Y%m%d_%H%M}.gpx",
                               mime="application/gpx+xml", width="stretch", key="btn_gpx")
            st.caption("GPX bisa diimpor ke aplikasi GPS lain yang punya alarm titik — berguna "
                       "bila Anda ingin alarm tetap jalan saat aplikasi ini tidak di layar.")
            if st.button("🔁 Geocode ulang yang gagal", width="stretch", key="btn_ulang"):
                geocode_ulang_yang_gagal()
            if not st.session_state.get("_konfirmasi_hapus"):
                if st.button("🗑️ Hapus semua data", width="stretch", key="btn_hapus"):
                    st.session_state._konfirmasi_hapus = True
                    st.rerun()
            else:
                st.warning(f"Hapus {len(data)} LP dari aplikasi **dan dari penyimpanan HP ini**? "
                           "Tidak bisa dibatalkan (kecuali Anda punya CSV-nya).")
                kiri, kanan = st.columns(2)
                with kiri:
                    if st.button("Ya, hapus", type="primary", width="stretch", key="btn_hapus_ya"):
                        st.session_state.data_lp = {}
                        st.session_state.antrian = []
                        st.session_state.batch = {}
                        st.session_state.jumlah_tampil = KARTU_PER_HALAMAN
                        st.session_state._konfirmasi_hapus = False
                        st.rerun()
                with kanan:
                    if st.button("Batal", width="stretch", key="btn_hapus_batal"):
                        st.session_state._konfirmasi_hapus = False
                        st.rerun()


def form_koreksi(r: dict) -> None:
    """Surveyor bisa menempelkan koordinat hasil cek lapangan / Google Maps."""
    with st.form(f"koreksi_{r['id']}", border=False):
        isian = st.text_input("Koordinat TKP yang benar",
                              placeholder="-6.89412, 110.63785 atau link Google Maps",
                              help="Di Google Maps: tekan lama titik TKP → salin koordinat.",
                              key=f"isian_koreksi_{r['id']}")
        if st.form_submit_button("💾 Simpan koordinat", width="stretch",
                                 key=f"simpan_koreksi_{r['id']}"):
            k = parse_koordinat(isian)
            if not k:
                st.error("Koordinat tidak valid / di luar Indonesia.")
            else:
                r.update({"lat": k[0], "lon": k[1], "status": STATUS_MANUAL,
                          "presisi": PRESISI_MANUAL, "alasan": "",
                          "validasi": "Diinput manual oleh surveyor"})
                st.rerun()


def kartu_lp(r: dict, jarak_km: float | None) -> None:
    """Satu LP = satu Card (bukan tabel lebar yang terpotong di HP)."""
    ada_titik = r.get("lat") is not None and r.get("lon") is not None
    emoji = EMOJI_PRESISI.get(r.get("presisi"), "⚠️") if ada_titik else "⚠️"
    if r.get("selesai"):
        emoji = "✅"
    with st.container(border=True):
        st.markdown(f"**{emoji} {_md(r.get('no_lp') or r['file'])}**")
        baris = []
        if jarak_km is not None:
            baris.append(f"📏 **{_fmt_km(jarak_km)}** dari posisi Anda")
        kasar = ada_titik and r.get("presisi") in PRESISI_KASAR
        if ada_titik:
            baris.append(f"🎯 Presisi titik: **{_md(r.get('presisi'))}**")
            if kasar:
                baris.append("⚠️ *Titik perkiraan, bukan lokasi TKP persis — cek lewat "
                             "tombol Cari, lalu simpan koordinat yang benar di Detail.*")
        else:
            baris.append(f"❗ **{STATUS_GAGAL}** — {_md(r.get('alasan'))}")
        if r.get("tkp"):
            baris.append(f"📍 {_md(_potong(r['tkp'], 170))}")
        wilayah = " · ".join(x for x in [
            f"Dsn. {r['dusun']}" if r.get("dusun") else "",
            f"Ds. {r['desa']}" if r.get("desa") else "",
            f"Kec. {r['kecamatan']}" if r.get("kecamatan") else "",
            f"{r.get('jenis_wilayah') or 'Kab/Kota'} {r['kabupaten']}" if r.get("kabupaten") else "",
        ] if x)
        if wilayah:
            baris.append(f"🏘️ {_md(wilayah)}")
        if r.get("patokan"):
            baris.append(f"🚩 Patokan: {_md(_potong(r['patokan'], 90))}")
        if r.get("waktu"):
            baris.append(f"🕒 {_md(r['waktu'])}")
        st.markdown("  \n".join(baris))
        st.caption(f"📄 {r['file']}")

        if ada_titik:
            st.link_button("🧭 Mulai Survei / Navigasi", url_navigasi(r["lat"], r["lon"]),
                           type="primary", width="stretch")
        q = teks_cari_google(r)
        if q and (kasar or not ada_titik):
            st.link_button(f"🔎 Cari “{_md(_potong(q, 40))}” di Google Maps", url_cari(q),
                           width="stretch")
        if ada_titik:
            # Nilai dibaca ulang di awal main() (sinkron_status_survei) agar peta,
            # judul card & alarm langsung ikut berubah pada putaran yang sama.
            st.checkbox("✅ Sudah disurvei (alarm TKP ini dimatikan)",
                        value=bool(r.get("selesai")), key=f"selesai_{r['id']}")

        with st.expander("ℹ️ Detail & koreksi titik"):
            detail = [
                f"**Sumber alamat:** {_md(r.get('sumber_tkp') or '-')}",
                f"**Sumber kab/kota:** {_md(r.get('sumber_wilayah') or '-')}",
                f"**Patokan dicari:** {_md(r.get('poi') or '-')}",
                f"**Jalan:** {_md(r.get('jalan') or '-')}",
                f"**Polres:** {_md(r.get('polres') or '-')}",
                f"**Query geocoding:** {_md(r.get('query') or '-')}",
                f"**Validasi:** {_md(r.get('validasi') or '-')}",
                f"**Alamat hasil geocoder:** {_md(r.get('alamat_geocoder') or '-')}",
            ]
            if ada_titik:
                detail.append(f"**Koordinat:** `{r['lat']:.6f}, {r['lon']:.6f}`")
            st.markdown("  \n".join(detail))
            form_koreksi(r)


def sinkron_status_survei(data: dict) -> None:
    """Salin nilai checkbox 'Sudah disurvei' ke data sebelum peta & alarm dibuat."""
    for r in data.values():
        kunci = f"selesai_{r['id']}"
        if kunci in st.session_state:
            r["selesai"] = bool(st.session_state[kunci])


def _cocok_pencarian(r: dict, kata: str) -> bool:
    if not kata:
        return True
    gabung = " ".join(str(r.get(k) or "") for k in
                      ("no_lp", "file", "tkp", "jalan", "poi", "dusun", "desa", "kecamatan",
                       "kabupaten"))
    return all(k in gabung.lower() for k in kata.lower().split())


# =============================================================================
# 10. APLIKASI UTAMA
# =============================================================================
def main() -> None:
    st.set_page_config(page_title="Survei TKP Laka", page_icon="🚑", layout="wide",
                       initial_sidebar_state="collapsed")
    st.markdown(CSS_MOBILE, unsafe_allow_html=True)
    if not cek_akses():
        st.stop()

    st.session_state.setdefault("data_lp", {})
    st.session_state.setdefault("gps", None)
    st.session_state.setdefault("jumlah_tampil", KARTU_PER_HALAMAN)
    st.session_state.setdefault("antrian", [])      # dokumen menunggu diproses
    st.session_state.setdefault("batch", {})

    if st.session_state.get("pesan_toast"):
        st.toast(st.session_state.pop("pesan_toast"))

    st.markdown("### 🚑 Survei TKP Laka")
    wadah_peta = st.container()          # peta diisi belakangan, tapi tampil paling atas
    wadah_ponsel = st.container()        # alarm TKP + status penyimpanan HP (di bawah peta)

    sinkron_status_survei(st.session_state.data_lp)
    gps, radius = panel_lokasi()
    panel_upload()
    tampilkan_peta_dan_daftar(wadah_peta, gps, radius)

    # Komponen HP dipanggil PALING AKHIR agar menerima data terbaru (termasuk
    # hasil proses & koreksi pada putaran ini) lalu langsung menyimpannya di HP.
    with wadah_ponsel:
        sinkron_ponsel()
    if st.session_state.antrian:         # masih ada antrean → lanjut putaran berikutnya
        st.rerun()


def tampilkan_peta_dan_daftar(wadah_peta, gps: dict | None, radius: int) -> None:
    # --- Analisis spasial: jarak tiap TKP ke posisi surveyor
    data = st.session_state.data_lp
    semua = list(data.values())
    titik = [r for r in semua if r.get("lat") is not None and r.get("lon") is not None]
    gagal = [r for r in semua if r.get("lat") is None or r.get("lon") is None]
    jarak = {r["id"]: haversine_km(gps["lat"], gps["lon"], r["lat"], r["lon"])
             for r in titik} if gps else {}
    id_dalam = {i for i, d in jarak.items() if d <= radius}

    with wadah_peta:
        # Objek peta dipakai ulang selama data/GPS/radius sama: HTML-nya identik,
        # sehingga Streamlit tidak mengirim ulang ratusan KB ke HP di tiap interaksi.
        sidik = sidik_peta(titik, gps, radius)
        if st.session_state.get("_peta_sidik") != sidik:
            st.session_state._peta = buat_peta(titik, gps, radius, id_dalam)
            st.session_state._peta_sidik = sidik
        st_folium(st.session_state._peta, key=f"peta_{sidik}",
                  height=TINGGI_PETA, use_container_width=True, returned_objects=[])
        st.caption("🔴 Patokan/jalan · 🟠 Dusun/desa · 🔵 Pusat kecamatan (perkiraan) · "
                   "🟣 Manual · 🟢 Sudah disurvei · ⚪ Di luar radius")

    if not semua:
        st.info("Upload LP (PDF / Word) untuk mulai memetakan TKP.")
        return

    # --- Ringkasan + pencarian
    ringkas = f"**📄 {len(semua)} LP** · ✅ {len(titik)} terpetakan · ⚠️ {len(gagal)} cek manual"
    if gps:
        ringkas += f" · 🎯 **{len(id_dalam)} dalam {radius} km**"
    st.markdown(ringkas)
    kata = st.text_input("Cari LP", placeholder="🔎 Cari No. LP / jalan / desa / kecamatan",
                         label_visibility="collapsed", key="kata_cari")

    # --- Daftar Card: HANYA TKP di dalam radius (diurutkan dari yang terdekat)
    if gps:
        daftar = sorted((r for r in titik if r["id"] in id_dalam), key=lambda r: jarak[r["id"]])
        st.markdown(f"#### 📍 TKP dalam radius {radius} km")
        sisa_luar = len(titik) - len(id_dalam)
        if sisa_luar:
            st.caption(f"{sisa_luar} TKP lain di luar radius disembunyikan — geser slider untuk memperluas.")
    else:
        daftar = sorted(titik, key=lambda r: (r.get("kabupaten", ""), r.get("kecamatan", "")))
        st.markdown("#### 🗺️ Semua TKP terpetakan")
        st.caption("Aktifkan GPS (tombol 📍) agar daftar difilter sesuai radius survei.")
    daftar = [r for r in daftar if _cocok_pencarian(r, kata)]

    if not daftar:
        st.info("Tidak ada TKP pada filter ini.")
    tampil = daftar[: st.session_state.jumlah_tampil]
    for r in tampil:
        kartu_lp(r, jarak.get(r["id"]))
    if len(daftar) > len(tampil):
        sisa = len(daftar) - len(tampil)
        st.button(f"Tampilkan {min(KARTU_PER_HALAMAN, sisa)} lagi ({sisa} tersisa)",
                  width="stretch", key="btn_lagi", on_click=_tambah_tampil)

    # --- LP yang gagal dipetakan (toggle, bukan expander, agar tidak bersarang)
    if gagal:
        st.divider()
        if st.toggle(f"⚠️ Tampilkan LP perlu cek manual ({len(gagal)})", key="tgl_gagal"):
            daftar_gagal = [r for r in gagal if _cocok_pencarian(r, kata)]
            for r in daftar_gagal[:50]:
                kartu_lp(r, None)
            if len(daftar_gagal) > 50:
                st.caption(f"{len(daftar_gagal) - 50} lainnya — gunakan kolom pencarian.")

    st.caption("🔐 File LP hanya dibaca di memori server (tidak disimpan di server). Hasil "
               "olahan disimpan di browser HP ini saja. Yang dikirim ke Nominatim/OSM hanya "
               "nama patokan, jalan, dusun, desa, kecamatan, dan kabupaten/kota.")


def _tambah_tampil() -> None:
    st.session_state.jumlah_tampil += KARTU_PER_HALAMAN


if __name__ == "__main__":   # `streamlit run app.py` menjalankan skrip sebagai __main__
    main()
