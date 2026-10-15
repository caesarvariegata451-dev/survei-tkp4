"""
=====================================================================
 SURVEI TKP LAKA LANTAS — V3 ULTIMATE
 Jasa Raharja · Divisi Klaim (aplikasi internal, mobile-first)
---------------------------------------------------------------------
 Fungsi ganda:
   1) Alat navigasi survei TKP di lapangan (HP Android)
   2) Dashboard monitoring angka laka lantas

 Alur kerja lapangan:
   Lihat peta → 🧭 Mulai Navigasi → tiba di TKP → ketik nama korban /
   nomor LP di kolom cari → buka kartu → ✅ Tandai Sudah Disurvei

 Jalankan lokal :  streamlit run app.py
 Data status    :  database_laka.csv (satu folder dengan app.py)
=====================================================================
"""

from __future__ import annotations

import hashlib
import html
import io
import math
import os
import re
import tempfile
import threading
import unicodedata
from datetime import date, datetime, timedelta, timezone
from difflib import SequenceMatcher
from pathlib import Path
from urllib.parse import quote_plus

import folium
import pandas as pd
import pdfplumber
import streamlit as st
from branca.element import MacroElement
from folium.plugins import Fullscreen, HeatMap, LocateControl, MarkerCluster
from geopy.exc import GeopyError
from geopy.extra.rate_limiter import RateLimiter
from geopy.geocoders import Nominatim
from jinja2 import Template
from streamlit_folium import st_folium

try:  # GPS sisi-server (untuk hitung jarak & urutkan TKP terdekat) — opsional
    from streamlit_js_eval import streamlit_js_eval
except ImportError:  # aplikasi tetap jalan tanpa paket ini
    streamlit_js_eval = None


# =====================================================================
# 0. KONFIGURASI
# =====================================================================
APP_DIR = Path(__file__).resolve().parent
DB_PATH = Path(os.environ.get("LAKA_DB_PATH", APP_DIR / "database_laka.csv"))

WIB = timezone(timedelta(hours=7), "WIB")

# Tile Google Maps sesuai permintaan, memakai https: aplikasi di Streamlit Cloud
# berjalan di https, tile http akan dianggap "mixed content" oleh browser HP.
GOOGLE_TILE_JALAN = "https://mt0.google.com/vt/lyrs=m&hl=en&x={x}&y={y}&z={z}"
GOOGLE_TILE_SATELIT = "https://mt0.google.com/vt/lyrs=y&hl=en&x={x}&y={y}&z={z}"

# Nominatim (OpenStreetMap) wajib diberi identitas aplikasi + kontak.
# GANTI email di bawah dengan email kantor Anda.
NOMINATIM_USER_AGENT = "jr-survei-tkp/3.0 (internal; kontak: ganti-email-anda@contoh.id)"
JEDA_GEOCODE_DETIK = 1.1  # kebijakan Nominatim: maksimal 1 permintaan/detik

STATUS_BELUM = "Belum Disurvei"
STATUS_SUDAH = "Sudah Disurvei"

FILTER_BELUM = "Belum Disurvei"
FILTER_SUDAH = "Sudah Disurvei"
FILTER_SEMUA = "Tampilkan Semua (Monitoring)"
LABEL_FILTER = {
    FILTER_BELUM: "🔴 Belum Disurvei",
    FILTER_SUDAH: "🟢 Sudah Disurvei",
    FILTER_SEMUA: "🗂️ Tampilkan Semua (Monitoring)",
}

# Tingkat akurasi titik peta (hasil geocoding berlapis)
AKURASI_GPS = "GPS Surveyor"
AKURASI_PERKIRAAN = {"Desa + Kecamatan", "Kecamatan + Kabupaten"}
AKURASI_BELUM = "Belum diproses"
AKURASI_GAGAL = "Tidak ditemukan"
AKURASI_TERTUNDA = "Tertunda (layanan peta sibuk)"
AKURASI_PERLU_ULANG = {AKURASI_BELUM, AKURASI_GAGAL, AKURASI_TERTUNDA, ""}

KONDISI_LABEL = {"MD": "Meninggal Dunia", "LB": "Luka Berat", "LR": "Luka Ringan"}

DEFAULT_CENTER = (-2.5, 118.0)  # titik tengah Indonesia (dipakai jika belum ada data)

KOLOM_DB = [
    "id", "nomor_lp", "nama_korban", "alamat_tkp", "uraian", "ringkasan",
    "kondisi_korban", "tanggal_kejadian",
    "jalan", "desa", "kecamatan", "kabupaten",
    "lat", "lon", "akurasi_lokasi",
    "status", "waktu_survei", "surveyor",
    "nama_file", "file_hash", "waktu_input", "catatan",
]


# =====================================================================
# 1. UTILITAS TEKS & WAKTU
# =====================================================================
def sekarang_wib() -> datetime:
    return datetime.now(WIB)


def waktu_str(dt: datetime | None = None) -> str:
    return (dt or sekarang_wib()).strftime("%Y-%m-%d %H:%M")


def rapikan_spasi(teks: str) -> str:
    return re.sub(r"\s+", " ", teks or "").strip()


def esc(teks) -> str:
    """Escape HTML agar teks dari PDF tidak merusak tampilan kartu/popup."""
    return html.escape(str(teks or ""), quote=True)


def normalisasi_teks_pdf(teks: str) -> str:
    """Bersihkan artefak PDF: ligatur, NBSP, titik dua lebar, spasi ganda, nomor halaman."""
    teks = unicodedata.normalize("NFKC", teks or "")
    teks = teks.replace("\u00a0", " ").replace("\t", " ").replace("\r\n", "\n").replace("\r", "\n")
    baris = []
    for b in teks.split("\n"):
        b = re.sub(r"[ ]{2,}", " ", b).strip()
        if re.fullmatch(r"-\s*\d+\s*-|hal(?:aman)?\.?\s*\d+(?:\s*(?:dari|/)\s*\d+)?", b, re.I):
            continue  # buang penanda halaman "- 2 -" / "Hal 1 dari 3"
        baris.append(b)
    return "\n".join(baris)


# Singkatan yang titiknya BUKAN akhir kalimat (dipakai pemecah kalimat)
_SINGKATAN = {
    "jl", "jln", "gg", "ds", "dsn", "dk", "dkh", "kp", "kel", "kec", "kab", "prov", "no", "nopol",
    "pol", "sdr", "sdri", "sdra", "tn", "ny", "nn", "bpk", "an", "km", "rt", "rw", "tgl", "th",
    "thn", "dr", "hj", "alm", "almh", "dkk", "dll", "dsb", "spt", "kom", "ipda", "iptu", "aiptu",
    "aipda", "bripka", "brigpol", "briptu", "bripda", "pt", "cv", "moh", "muh", "mhd", "st",
}
_RE_TITIK_KALIMAT = re.compile(r"([.!?])\s+(?=[A-Z0-9\"'(])")


def pecah_kalimat(teks: str) -> list[str]:
    """Pemecah kalimat yang paham singkatan Indonesia (Jl., Ds., Kec., Sdr., No.Pol, dll)."""
    hasil, awal = [], 0
    for m in _RE_TITIK_KALIMAT.finditer(teks):
        kata = re.search(r"([A-Za-z]+)$", teks[awal:m.start()])
        if m.group(1) == "." and kata and (kata.group(1).lower() in _SINGKATAN or len(kata.group(1)) == 1):
            continue
        hasil.append(teks[awal:m.end()].strip())
        awal = m.end()
    sisa = teks[awal:].strip()
    if sisa:
        hasil.append(sisa)
    return [k for k in hasil if k]


# =====================================================================
# 2. EKSTRAKSI PDF — REGEX BERLAPIS + NLP BERBASIS ATURAN
# =====================================================================
_NOMOR_BUTIR = r"(?:[A-Za-z0-9]{1,3}[.)]\s*)?"  # "1.", "a.", "II.", "b)"
RE_KOP_LP = re.compile(r"L\s*A\s*P\s*O\s*R\s*A\s*N\s+P\s*O\s*L\s*I\s*S\s*I", re.I)
# Judul dokumen LP = baris yang HANYA berisi "LAPORAN POLISI" (bukan frasa dalam surat pengantar)
RE_JUDUL_LP = re.compile(
    r"^\s*L\s*A\s*P\s*O\s*R\s*A\s*N\s+P\s*O\s*L\s*I\s*S\s*I(?:\s+(?:MODEL\s+)?[A-Z])?\s*:?\s*"
    r"(?:(?:Nomor|No\.?)\s*:?.*)?$", re.I | re.M)
RE_NOMOR_LP = re.compile(
    r"\bL\s?P\s*[/\-.]\s*(?:[A-Z]{1,2}\s*[/\-.]\s*)?\d{1,6}\s*[/\-.][^\n]*", re.I)
RE_LABEL_NOMOR_LP = re.compile(
    r"(?:Nomor|No\.?)\s*(?:LP|Laporan(?:\s+Polisi)?)\s*[:.]?\s*([A-Z0-9][^\n]{4,})", re.I)

# Kata kunci awal bagian/label lain → tanda berhenti saat mengambil nilai multi-baris
_KATA_BAGIAN = (
    r"(?:apa\s+yang\s+terjadi|siapa\b|bagaimana|dilaporkan|uraian|tindak\s+pidana|saksi|"
    r"barang\s+bukti|tindakan|waktu\s+kejadian|hari\s*/?\s*tanggal|peristiwa|yang\s+melapor|"
    r"korban|terlapor|pelapor|mengetahui|demikian|kronolog|kesimpulan|kendaraan|pasal)"
)
RE_AWAL_BAGIAN = re.compile(rf"^\s*{_NOMOR_BUTIR}{_KATA_BAGIAN}", re.I)
RE_LABEL_UMUM = re.compile(rf"^\s*{_NOMOR_BUTIR}[A-Za-z][A-Za-z /&.()\-]{{1,40}}?\s*:\s*")

RE_LABEL_TKP = re.compile(
    rf"^\s*{_NOMOR_BUTIR}(?:(?:alamat\s+)?tempat\s+kejadian(?:\s+perkara)?|lokasi\s+(?:kejadian|tkp|kecelakaan)"
    rf"|alamat\s+tkp|tkp|tempat\s+kecelakaan)(?:\s*/\s*[A-Za-z]+)?\s*:\s*(.*)$", re.I)
RE_LABEL_WAKTU_TEMPAT = re.compile(
    rf"^\s*{_NOMOR_BUTIR}waktu\s+(?:dan|&)\s+tempat\s+kejadian\s*:\s*(.*)$", re.I)
RE_TKP_NARASI = re.compile(
    r"\bdi\s+((?:Jl|Jln|Jalan|Gg|Ds|Desa|Dsn|Dusun|Dk|Dukuh|Kel|Kelurahan|Kp|Kampung|Simpang|"
    r"Perempatan|Pertigaan|Jembatan|Tol)\b.{5,180}?)"
    r"(?=\s*,?\s*(?:telah\s+terjadi|terjadi\s+(?:kecelakaan|laka)|yang\s+melibatkan)\b)", re.I | re.S)

RE_LABEL_KORBAN = re.compile(
    rf"^\s*{_NOMOR_BUTIR}(?:(?:pelapor|pengemudi|pengendara|penumpang|pejalan\s+kaki)\s*/\s*)?"
    r"(?:nama\s+|identitas\s+|data\s+)?korban(?:\s+(?:ke[\s-]?)?(?:\d{1,2}|[IVX]{1,4}))?\s*:\s*(.*)$", re.I)
RE_KOP_KORBAN = re.compile(rf"^\s*{_NOMOR_BUTIR}(?:identitas|data)?\s*korban\s*:?\s*$", re.I)
RE_FIELD_NAMA = re.compile(rf"^\s*{_NOMOR_BUTIR}nama(?:\s+lengkap)?\s*:\s*(.+)$", re.I)
RE_STOP_BLOK_KORBAN = re.compile(
    rf"^\s*{_NOMOR_BUTIR}(?:terlapor|pelapor|saksi|bagaimana|dilaporkan|uraian|barang\s+bukti|tindakan|"
    r"tindak\s+pidana|apa\s+yang\s+terjadi|kendaraan|kronolog)", re.I)
_GELAR = r"(?:sdr[ia]?|saudar[ai]|tn|ny|nn|nona|bpk|bapak|ibu|an|a\s?\.\s?n|alm|almh|almarhum(?:ah)?|mr|mrs|ms)"
RE_KORBAN_NARASI = [
    re.compile(
        r"(?i:\bkorban\s+(?:yang\s+)?(?:bernama|atas\s+nama|a\.\s?n\.?|an\.))\s*"
        r"(?:(?i:sdr[ia]?|tn|ny|nn|bpk|ibu)\.?\s*)?(?P<n>[A-Z][A-Za-z.'\-]*(?:\s+[A-Z][A-Za-z.'\-]*){0,4})"),
    re.compile(
        r"(?i:\b(?:mengakibatkan|menyebabkan)\s+(?:(?:pengendara|pengemudi|penumpang|pejalan\s+kaki|pembonceng)\s+)?"
        r"(?:(?:sepeda\s+motor|mobil|kendaraan)\s+)?(?:sdr[ia]?|saudar[ai]|tn|ny|an)\.?)\s*"
        r"(?P<n>[A-Z][A-Za-z.'\-]*(?:\s+[A-Z][A-Za-z.'\-]*){0,4})"),
]
_POTONG_NAMA = re.compile(
    r"[,;:(\[/]|\s(?:umur|usia|lahir|tgl|tanggal|thn|tahun|th|laki[\s-]*laki|perempuan|pria|wanita|lk|pr|"
    r"alamat|pekerjaan|agama|warga|wni|jenis|status|mengalami|menderita|yang|selaku|sebagai|pengendara|"
    r"pengemudi|penumpang|pejalan|pembonceng|dengan|meninggal|luka|tewas|bertempat|tinggal|asal|nik|"
    r"dirawat|dibawa|meninggalkan)\b|\s\d", re.I)
_BUKAN_NAMA = {
    "TIDAK ADA", "NIHIL", "TIDAK DIKETAHUI", "BELUM DIKETAHUI", "TERLAMPIR", "TERLAPOR", "PELAPOR",
    "KORBAN", "SAKSI", "IDEM", "SDA", "DALAM PENYELIDIKAN", "DALAM LIDIK", "DATA TERLAMPIR", "LIHAT LAMPIRAN",
}
_KATA_TERLARANG_NAMA = {
    "MENGALAMI", "KENDARAAN", "SEPEDA", "MOTOR", "MOBIL", "TRUK", "BUS", "JALAN", "JL", "DESA", "KECAMATAN",
    "KABUPATEN", "KEC", "KAB", "LUKA", "MENINGGAL", "DUNIA", "TERSEBUT", "TELAH", "TERJADI", "KECELAKAAN",
    "LALU", "LINTAS", "PADA", "HARI", "DI", "KE", "DARI", "YANG", "SEBAGAIMANA", "BERDASARKAN", "LAPORAN",
    "POLISI", "NOMOR", "NAMA", "UMUR", "ALAMAT",
}

RE_KOP_URAIAN = [  # urutan = prioritas
    ("kesimpulan", re.compile(
        rf"^\s*{_NOMOR_BUTIR}kesimpulan(?:\s+(?:kejadian|kronologi\w*|laka|sementara|penyidik))?\s*:?\s*(.*)$", re.I)),
    ("uraian", re.compile(
        rf"^\s*{_NOMOR_BUTIR}(?:uraian\s+singkat(?:\s+(?:yang\s+dilaporkan|kejadian|peristiwa|perkara))?"
        r"|uraian\s+(?:kejadian|peristiwa)|kronologi(?:s)?(?:\s+(?:singkat|kejadian|laka|kecelakaan))?"
        r"|duduk\s+perkara)\s*:?\s*(.*)$", re.I)),
    ("bagaimana", re.compile(
        rf"^\s*{_NOMOR_BUTIR}bagaimana\s+(?:terjadi(?:nya)?|kejadian\w*)\s*:?\s*(.*)$", re.I)),
]
RE_STOP_URAIAN = re.compile(
    rf"^\s*{_NOMOR_BUTIR}(?:tindakan\s+yang\s+(?:diambil|dilakukan)|barang\s+bukti|nama\s+dan\s+alamat\s+saksi|"
    r"saksi[\s-]*saksi|demikian|mengetahui|yang\s+menerima\s+laporan|yang\s+melapor|pelapor\s*[:,]|"
    r"tindak\s+pidana\s+apa|kerugian|catatan\s*:|dilaporkan\s+pada|an\.\s*kepala|kepala\s+(?:satuan|unit|kepolisian))",
    re.I)
RE_TEMPAT_TANGGAL = re.compile(r"^[A-Za-z .]{3,30},\s*\d{1,2}\s+[A-Za-z]+\.?\s+\d{4}\s*$")  # "Blora, 13 Oktober 2026"

_BULAN = {
    "januari": 1, "jan": 1, "februari": 2, "pebruari": 2, "feb": 2, "peb": 2, "maret": 3, "mar": 3,
    "april": 4, "apr": 4, "mei": 5, "juni": 6, "jun": 6, "juli": 7, "jul": 7, "agustus": 8, "agu": 8,
    "agt": 8, "ags": 8, "aug": 8, "september": 9, "sept": 9, "sep": 9, "oktober": 10, "okt": 10,
    "oct": 10, "november": 11, "nopember": 11, "nov": 11, "nop": 11, "desember": 12, "des": 12, "dec": 12,
}
RE_TGL_TEKS = re.compile(
    r"\b(\d{1,2})\s*[-\s]\s*(" + "|".join(sorted(_BULAN, key=len, reverse=True)) + r")\.?\s*[-\s]\s*(\d{4})\b", re.I)
RE_TGL_ANGKA = re.compile(r"\b(\d{1,2})[-/.](\d{1,2})[-/.](\d{4})\b")

# Bobot kata kunci untuk peringkas kronologi (extractive summarization)
_BOBOT_KALIMAT = [
    (r"telah\s+terjadi|terjadi\s+(?:kecelakaan|laka)", 3),
    (r"kecelakaan|\blaka\b|tabrak|bertabrakan|terjatuh|tergelincir|terserempet|menyerempet|terguling|terlindas", 2),
    (r"mengakibatkan|akibat(?:nya)?|sehingga|menyebabkan", 2),
    (r"meninggal\s+dunia|tewas|luka\s+berat|luka\s+ringan|luka[\s-]+luka|dirawat|rumah\s+sakit|\bRS\b|puskesmas", 3),
    (r"dikemudikan|pengendara|pengemudi|sepeda\s+motor|mobil|truk|\bbus\b|pejalan\s+kaki|no\.?\s?pol", 1),
    (r"\bjl\b|jalan|\bkm\b|desa|\bds\b|kec\b|kecamatan", 1),
    (r"pukul|sekira|sekitar\s+jam", 1),
]


_KATA_ALAMAT = re.compile(
    r"\b(?:JL|JLN|JALAN|GG|GANG|DS|DESA|DSN|DUSUN|DK|DKH|DUKUH|KEL|KELURAHAN|KEC|KECAMATAN|KAB|KABUPATEN|KOTA|"
    r"PROV|PROVINSI|RT|RW|KM|KP|KAMPUNG|NO)\b")


def _judul_bagian(b: str) -> bool:
    """Baris judul bagian berhuruf kapital ("IDENTITAS KORBAN") yang bukan potongan alamat."""
    s = b.strip()
    return len(s) >= 6 and s == s.upper() and bool(re.search(r"[A-Z]{3}", s)) and not _KATA_ALAMAT.search(s)


def _ambil_lanjutan(baris: list[str], idx: int, nilai: str, maks_baris: int = 3) -> str:
    """Ambil nilai label + baris lanjutannya (alamat sering terpotong ke baris berikut)."""
    bagian = [nilai] if nilai else []
    for b in baris[idx + 1: idx + 1 + maks_baris]:
        if (not b.strip() or RE_AWAL_BAGIAN.match(b) or RE_LABEL_UMUM.match(b) or RE_KOP_LP.search(b)
                or _judul_bagian(b)):
            break
        bagian.append(b)
    return rapikan_spasi(" ".join(bagian))


def bersihkan_nomor_lp(raw: str) -> str:
    s = re.split(r"\s+(?:tanggal|tgl\.?|tentang|perihal|pada|hari)\b|[,;]", raw or "", maxsplit=1, flags=re.I)[0]
    s = re.sub(r"\s*([/\-])\s*", r"\1", s)
    s = re.sub(r"\b(LP)\s*\.\s*", r"\1.", s, flags=re.I)  # "LP. 123/…" → "LP.123/…"
    return rapikan_spasi(s).strip(" .-/:").upper()


def _lp_valid(s: str) -> bool:
    return bool(s) and bool(re.search(r"\d", s)) and len(re.findall(r"[/\-.]", s)) >= 2 and len(s) >= 8


def ekstrak_nomor_lp(teks: str) -> str:
    baris = teks.split("\n")
    # Utamakan nomor yang berada tepat di bawah judul "LAPORAN POLISI"
    judul = [i for i, b in enumerate(baris) if RE_JUDUL_LP.match(b)]
    urutan = list(range(judul[0], min(judul[0] + 6, len(baris)))) if judul else []
    prioritas = set(urutan)
    urutan += [i for i in range(len(baris)) if i not in prioritas]
    for i in urutan:
        b = baris[i]
        m = RE_NOMOR_LP.search(b)
        if not m:
            continue
        raw = m.group(0).strip()
        # Nomor LP panjang kadang terpotong ke baris berikut ("…/POLRES BLORA/" ↵ "POLDA JAWA TENGAH")
        if raw.endswith("/") and i + 1 < len(baris) and 0 < len(baris[i + 1]) < 60 \
                and not RE_LABEL_UMUM.match(baris[i + 1]):
            raw += baris[i + 1].strip()
        nomor = bersihkan_nomor_lp(raw)
        if _lp_valid(nomor):
            return nomor
    m = RE_LABEL_NOMOR_LP.search(teks)
    if m:
        nomor = bersihkan_nomor_lp(m.group(1))
        if _lp_valid(nomor):
            return nomor
    return ""


def bersihkan_nama(raw: str) -> str:
    s = rapikan_spasi(raw)
    if re.search(r"\bmr\.?\s*x\b", s, re.I):
        return "MR. X"  # korban tanpa identitas
    s = re.sub(r"^(?:\d{1,2}[.)]\s*|[a-z][.)]\s+)+", "", s)  # nomor urut "1." / "a)" (bukan inisial "M.")
    s = re.sub(r"^nama(?:\s+lengkap)?\s*:\s*", "", s, flags=re.I)
    s = re.sub(rf"^(?:{_GELAR}\.?\s+)+", "", s, flags=re.I)
    s = _POTONG_NAMA.split(s, maxsplit=1)[0]
    s = re.sub(r"[^A-Za-z.'\- ]", " ", s)
    return rapikan_spasi(s).strip(" .-'").upper()


def nama_valid(s: str) -> bool:
    if not s or s in _BUKAN_NAMA:
        return False
    if s == "MR. X":
        return True
    kata = s.split()
    if len(re.sub(r"[^A-Z]", "", s)) < 3 or len(s) > 50 or len(kata) > 6:
        return False
    return not any(k.strip(".'-") in _KATA_TERLARANG_NAMA for k in kata)


def ekstrak_nama_korban(teks: str) -> list[str]:
    """Nama korban dari label 'Korban :', blok 'IDENTITAS KORBAN', lalu fallback narasi."""
    nama: list[str] = []

    def tambah(raw: str) -> None:
        for bagian in re.split(r"\s+dan\s+|;|\s(?=\d{1,2}[.)]\s)", raw):
            n = bersihkan_nama(bagian)
            if nama_valid(n) and n not in nama:
                nama.append(n)

    baris = teks.split("\n")
    for i, b in enumerate(baris):
        m = RE_LABEL_KORBAN.match(b)
        if not m and not RE_KOP_KORBAN.match(b):
            continue
        sebelum = len(nama)
        if m and m.group(1).strip():
            tambah(m.group(1))
        if len(nama) == sebelum:  # nama ada di baris-baris berikutnya ("Nama : …")
            for nb in baris[i + 1: i + 8]:
                if RE_STOP_BLOK_KORBAN.match(nb) or RE_LABEL_KORBAN.match(nb):
                    break
                mf = RE_FIELD_NAMA.match(nb)
                if mf:
                    tambah(mf.group(1))
                    break
    if not nama:
        for pola in RE_KORBAN_NARASI:
            for m in pola.finditer(teks):
                tambah(m.group("n"))
    return nama[:5]


def _alamat_valid(s: str) -> bool:
    return len(re.sub(r"[^A-Za-z]", "", s)) >= 5 and s.strip(" .-").lower() not in {"terlampir", "idem", "sda"}


def ekstrak_alamat_tkp(teks: str) -> str:
    baris = teks.split("\n")
    for i, b in enumerate(baris):
        m = RE_LABEL_TKP.match(b)
        if m:
            alamat = _ambil_lanjutan(baris, i, m.group(1).strip())
        else:
            m = RE_LABEL_WAKTU_TEMPAT.match(b)
            if not m:
                continue
            gabung = _ambil_lanjutan(baris, i, m.group(1).strip())
            potong = re.search(r"\bdi\s+(.+)$", gabung, re.I)  # "Senin … pukul 07.30 WIB di Jl. …"
            alamat = potong.group(1) if potong else ""
        alamat = re.sub(r"^(?:di|pada)\s+", "", rapikan_spasi(alamat), flags=re.I).strip(" ,.;:-")
        if _alamat_valid(alamat):
            return alamat
    m = RE_TKP_NARASI.search(rapikan_spasi(teks))  # fallback: "… di Jl. X … telah terjadi kecelakaan"
    if m:
        return m.group(1).strip(" ,.;:-")
    return ""


def _ambil_blok_uraian(baris: list[str], idx: int, awal: str, satu_butir: bool) -> str:
    bagian = [awal] if awal else []
    for b in baris[idx + 1: idx + 60]:
        if RE_STOP_URAIAN.match(b) or RE_KOP_LP.search(b) or RE_TEMPAT_TANGGAL.match(b) \
                or any(rx.match(b) for _, rx in RE_KOP_URAIAN):
            break
        if satu_butir and (RE_LABEL_UMUM.match(b) or RE_AWAL_BAGIAN.match(b)):
            break  # "Bagaimana terjadi :" hanya satu butir, berhenti di butir berikutnya
        bagian.append(b)
        if sum(len(x) for x in bagian) > 3500:
            break
    teks = rapikan_spasi(" ".join(bagian))
    teks = re.sub(r"^(?:sebagai\s+berikut|yaitu|adalah)\s*:?\s*", "", teks, flags=re.I)
    return re.sub(r"[-_=]{4,}", " ", teks).strip()


def ekstrak_uraian(teks: str) -> tuple[str, str]:
    """Kembalikan (uraian_lengkap, kesimpulan). Prioritas: KESIMPULAN > URAIAN SINGKAT > Bagaimana terjadi."""
    baris = teks.split("\n")
    temuan: dict[str, str] = {}
    for i, b in enumerate(baris):
        for jenis, rx in RE_KOP_URAIAN:
            m = rx.match(b)
            if m and jenis not in temuan:
                isi = _ambil_blok_uraian(baris, i, m.group(1).strip(), satu_butir=(jenis == "bagaimana"))
                if len(isi) >= 20:
                    temuan[jenis] = isi
                break
    uraian = temuan.get("uraian") or temuan.get("bagaimana") or ""
    if not uraian:  # fallback narasi tanpa judul bagian: mulai dari "Pada hari …" sebelum "telah terjadi"
        m = re.search(r"telah\s+terjadi\s+(?:kecelakaan|laka)", teks, re.I)
        if m:
            awal = teks.rfind("\n", 0, m.start()) + 1
            pada = list(re.finditer(r"\bPada\s+(?:hari|tanggal|tgl|malam|pagi|siang|sore)\b",
                                    teks[max(0, m.start() - 500): m.start()], re.I))
            if pada:
                awal = max(0, m.start() - 500) + pada[-1].start()
            bagian = []
            for b in teks[awal:].split("\n"):
                if bagian and (RE_STOP_URAIAN.match(b) or RE_JUDUL_LP.match(b) or RE_TEMPAT_TANGGAL.match(b)
                               or any(rx.match(b) for _, rx in RE_KOP_URAIAN)):
                    break
                bagian.append(b)
            uraian = " ".join(pecah_kalimat(rapikan_spasi(" ".join(bagian)))[:4])
    return uraian, temuan.get("kesimpulan", "")


def ringkas_kronologi(uraian: str, maks_kalimat: int = 3, maks_char: int = 480) -> str:
    """Peringkas ekstraktif: ambil kalimat berbobot tertinggi (kejadian, akibat, kondisi korban)
    selama muat di batas karakter, lalu susun ulang sesuai urutan aslinya."""
    uraian = rapikan_spasi(uraian)
    if not uraian:
        return ""
    kalimat = pecah_kalimat(uraian)
    if len(kalimat) <= maks_kalimat and len(uraian) <= maks_char:
        return uraian
    skor = []
    for i, k in enumerate(kalimat):
        s = sum(w for pola, w in _BOBOT_KALIMAT if re.search(pola, k, re.I))
        s += 2 if i == 0 else 0
        s -= 2 if len(k) < 25 else 0
        skor.append((s, i))
    pilih, panjang = [], 0
    for s, i in sorted(skor, key=lambda x: (-x[0], x[1])):
        if len(pilih) == maks_kalimat:
            break
        if pilih and (s <= 0 or panjang + len(kalimat[i]) + 1 > maks_char):
            continue  # lewati kalimat panjang berbobot rendah, coba kalimat berikutnya
        pilih.append(i)
        panjang += len(kalimat[i]) + 1
    hasil = " ".join(kalimat[i] for i in sorted(pilih))
    if len(hasil) > maks_char:  # satu kalimat inti pun sudah terlalu panjang
        hasil = hasil[:maks_char].rsplit(" ", 1)[0] + " …"
    return hasil


def _singkatan_kondisi(kode: str, teks: str) -> bool:
    """'MD'/'LB'/'LR' hanya dihitung jika jelas konteksnya ("korban … MD" atau "(MD)"),
    supaya inisial nama seperti "MD. RIDWAN" tidak salah terbaca sebagai meninggal dunia."""
    return bool(re.search(rf"(?i:korban|kondisi|keadaan)[^\n.]{{0,25}}\b{kode}\b|\(\s*{kode}\s*\)", teks))


def deteksi_kondisi(teks: str) -> str:
    """Tag kondisi korban terberat: MD / LB / LR (kata kunci + Pasal 310 UU 22/2009)."""
    if re.search(r"meninggal\s+dunia|\bmeninggal\b|\btewas\b|\bwafat\b", teks, re.I) or _singkatan_kondisi("MD", teks):
        return "MD"
    if re.search(r"luka\s+berat", teks, re.I) or _singkatan_kondisi("LB", teks):
        return "LB"
    if re.search(r"luka\s+ringan|luka[\s-]+luka|\blecet\b", teks, re.I) or _singkatan_kondisi("LR", teks):
        return "LR"
    pasal = re.search(r"pasal\s*310(.{0,60})", teks, re.I | re.S)  # ayat (4)=MD, (3)=LB, (2)=LR
    if pasal:
        ayat = pasal.group(1)
        for nomor, kode in (("4", "MD"), ("3", "LB"), ("2", "LR")):
            if re.search(rf"\(\s*{nomor}\s*\)|ayat\s*{nomor}\b", ayat, re.I):
                return kode
    return ""


def _parse_tanggal(teks: str) -> str:
    kandidat = []
    for m in RE_TGL_TEKS.finditer(teks):
        kandidat.append((m.start(), int(m.group(1)), _BULAN[m.group(2).lower()], int(m.group(3))))
    for m in RE_TGL_ANGKA.finditer(teks):
        kandidat.append((m.start(), int(m.group(1)), int(m.group(2)), int(m.group(3))))
    for _, d, mth, y in sorted(kandidat):
        try:
            tgl = date(y, mth, d)
        except ValueError:
            continue
        if 2000 <= tgl.year <= sekarang_wib().year + 1:
            return tgl.isoformat()
    return ""


def ekstrak_tanggal_kejadian(teks: str, uraian: str) -> str:
    baris = teks.split("\n")
    for i, b in enumerate(baris):
        if re.match(rf"^\s*{_NOMOR_BUTIR}(?:waktu(?:\s+(?:dan|&)\s+tempat)?\s+kejadian|hari\s*/\s*tanggal|tanggal\s+kejadian)",
                    b, re.I):
            tgl = _parse_tanggal(" ".join(baris[i: i + 2]))
            if tgl:
                return tgl
    return _parse_tanggal(uraian) or _parse_tanggal(teks)


# ---------- Komponen alamat (untuk geocoding berlapis) ----------
_EKSPANSI = [
    (r"\bJl(?:n)?\b\.?", "Jalan "), (r"\bGg\b\.?", "Gang "), (r"\bDs\b\.?", "Desa "),
    (r"\bDsn\b\.?", "Dusun "), (r"\bDk(?:h)?\b\.?", "Dukuh "), (r"\bKel\b\.?", "Kelurahan "),
    (r"\bKec\b\.?", "Kecamatan "), (r"\bKab\b\.?", "Kabupaten "), (r"\bProv\b\.?", "Provinsi "),
    (r"\bKp\b\.?", "Kampung "),
]
_STOP_JALAN = (r"(?:Jalan|Gang|Desa|Dusun|Dukuh|Kampung|Kelurahan|Kecamatan|Kabupaten|Kota|Provinsi|RT|RW|Km|No|"
               r"Nomor|depan|dekat|sebelah|samping|tepatnya|turut|ikut|masuk|arah|jurusan|wilayah)")
RE_JALAN = re.compile(rf"\b(?:Jalan|Gang)\s+(.+?)(?=\s*(?:[,;]|\.(?:\s|$)|\b{_STOP_JALAN}\b)|$)", re.I)
RE_DESA = re.compile(
    r"\b(?:Desa|Kelurahan)\s+([A-Za-z][A-Za-z'\- ]*?)(?=\s*(?:[,;.]|\b(?:RT|RW|Dusun|Dukuh|Kampung|Kecamatan|"
    r"Kabupaten|Kota|Provinsi|Jalan|Km|No)\b)|\s*$)", re.I)
RE_KECAMATAN = re.compile(
    r"\bKecamatan\s+([A-Za-z][A-Za-z'\- ]*?)(?=\s*(?:[,;.]|\b(?:Kabupaten|Kota|Kotamadya|Provinsi|Jalan|Desa|"
    r"Kelurahan|RT|RW)\b)|\s*$)", re.I)
_NAMA_WILAYAH = r"([A-Za-z][A-Za-z'\-]*(?:\s+[A-Za-z][A-Za-z'\-]*){0,3}?)"  # maksimal 4 kata
RE_KABUPATEN = re.compile(
    rf"\bKabupaten\s+{_NAMA_WILAYAH}(?=\s*(?:[,;.]|\b(?:Provinsi|Jalan|Desa|Kecamatan|RT|RW)\b)|\s*$)", re.I)
RE_KOTA = re.compile(
    rf"\bKota(?:madya)?\s+{_NAMA_WILAYAH}(?=\s*(?:[,;.]|\b(?:Provinsi|Jalan|Desa|Kecamatan|RT|RW)\b)|\s*$)", re.I)


def ekspansi_singkatan(alamat: str) -> str:
    s = alamat or ""
    for pola, ganti in _EKSPANSI:
        s = re.sub(pola, ganti, s, flags=re.I)
    return rapikan_spasi(s)


def _judul(s: str) -> str:
    return rapikan_spasi(s).strip(" -'").title()


def pecah_komponen_alamat(alamat: str) -> dict:
    s = ekspansi_singkatan(alamat)
    j, d, k = RE_JALAN.search(s), RE_DESA.search(s), RE_KECAMATAN.search(s)
    kb = RE_KABUPATEN.search(s) or RE_KOTA.search(s)
    return {
        "jalan": f"Jalan {_judul(j.group(1))}" if j and len(j.group(1).strip()) > 1 else "",
        "desa": _judul(d.group(1)) if d else "",
        "kecamatan": _judul(k.group(1)) if k else "",
        "kabupaten": _judul(kb.group(1)) if kb else "",
    }


def kabupaten_dari_konteks(nomor_lp: str, teks: str) -> str:
    """Jika alamat tak menyebut kabupaten, ambil dari nomor LP ('/POLRES BLORA/') atau kop 'RESOR BLORA'."""
    kandidat = [
        re.search(r"\b(?:POLRES(?:TA(?:BES)?)?|RES(?:TA)?)\s*\.?\s*(?:METRO\s+)?([A-Z][A-Z ]{2,30}?)\s*(?:/|$)",
                  nomor_lp or ""),
        re.search(r"^\s*(?:KEPOLISIAN\s+)?RESOR(?:\s+KOTA(?:\s+BESAR)?)?\s+([A-Z][A-Z ]{2,30})\s*$", teks, re.M),
    ]
    for m in kandidat:
        nama = _judul(m.group(1)) if m else ""
        # tolak singkatan seperti "SKA"/"SMG": nama singkatan bisa membuat semua kueri geocoding gagal
        if len(nama.replace(" ", "")) >= 4 and re.search(r"[aiueo]", nama, re.I):
            return nama
    return ""


def alamat_untuk_geocode(alamat: str) -> str:
    """Rapikan teks alamat LP agar lebih mudah dikenali Nominatim."""
    s = ekspansi_singkatan(alamat)
    s = re.sub(r"\bRT\.?\s*\d+\s*(?:/\s*RW\.?\s*\d+)?|\bRW\.?\s*\d+", " ", s, flags=re.I)
    s = re.sub(r"\bKm\.?\s*\d+(?:[.,]\d+)?", " ", s, flags=re.I)
    s = re.sub(r"\b(?:No|Nomor)\.?\s*\d+\w*", " ", s, flags=re.I)
    s = re.sub(r"\b(?:depan|dekat|sebelah|samping|tepatnya|turut|ikut|masuk|arah|jurusan)\b.*?"
               r"(?=,|\b(?:Desa|Kelurahan|Dusun|Kecamatan|Kabupaten|Kota|Provinsi)\b|$)", " ", s, flags=re.I)
    s = re.sub(r"\s*\b(?:Desa|Kelurahan|Dusun|Dukuh|Kampung|Kecamatan|Kabupaten|Kota(?:madya)?|Provinsi)\b\s*",
               ", ", s, flags=re.I)
    s = re.sub(r"\s*,\s*(?:,\s*)*", ", ", s)
    return rapikan_spasi(s).strip(" ,.-")


def ekstrak_lp(teks: str) -> dict:
    """Ekstrak semua entitas dari teks SATU dokumen LP."""
    nomor = ekstrak_nomor_lp(teks)
    korban = ekstrak_nama_korban(teks)
    alamat = ekstrak_alamat_tkp(teks)
    uraian, kesimpulan = ekstrak_uraian(teks)
    komponen = pecah_komponen_alamat(alamat)
    if not komponen["kabupaten"]:
        komponen["kabupaten"] = kabupaten_dari_konteks(nomor, teks)
    ringkasan = ringkas_kronologi(kesimpulan) if kesimpulan else ringkas_kronologi(uraian)
    return {
        "nomor_lp": nomor,
        "nama_korban": ", ".join(korban),
        "alamat_tkp": alamat,
        "uraian": uraian or kesimpulan,
        "ringkasan": ringkasan,
        # utamakan narasi kejadian; teks penuh hanya cadangan (template pasal bisa menyebut semua akibat)
        "kondisi_korban": deteksi_kondisi(f"{uraian} {kesimpulan}") or deteksi_kondisi(teks),
        "tanggal_kejadian": ekstrak_tanggal_kejadian(teks, uraian),
        **komponen,
    }


def catatan_kelengkapan(rec: dict) -> str:
    kurang = [label for kunci, label in (("nomor_lp", "Nomor LP"), ("nama_korban", "Nama Korban"),
                                         ("alamat_tkp", "Alamat TKP"), ("uraian", "Uraian"))
              if not rec.get(kunci)]
    return ("Tidak terbaca: " + ", ".join(kurang)) if kurang else ""


def baca_halaman_pdf(data: bytes) -> list[str]:
    with pdfplumber.open(io.BytesIO(data)) as pdf:
        return [normalisasi_teks_pdf(hal.extract_text() or "") for hal in pdf.pages]


def pecah_dokumen_lp(halaman: list[str]) -> list[str]:
    """Satu PDF bisa berisi beberapa LP (hasil scan digabung). Halaman yang diawali kop
    'LAPORAN POLISI' dengan nomor LP berbeda dianggap awal dokumen LP baru."""
    segmen: list[str] = []
    nomor_aktif = ""
    for teks in halaman:
        kepala = "\n".join(teks.split("\n")[:15])
        nomor = ekstrak_nomor_lp(kepala) if RE_JUDUL_LP.search(kepala) else ""
        if not segmen:
            segmen.append(teks)
            nomor_aktif = nomor
        elif nomor and nomor_aktif and nomor != nomor_aktif:
            segmen.append(teks)
            nomor_aktif = nomor
        else:
            segmen[-1] += "\n" + teks
            nomor_aktif = nomor_aktif or nomor
    return segmen


def buat_id(nomor_lp: str, file_hash: str, urutan: int) -> str:
    basis = re.sub(r"[^A-Z0-9]", "", nomor_lp.upper()) if nomor_lp else f"{file_hash}-{urutan}"
    return hashlib.md5(basis.encode()).hexdigest()[:12]


# =====================================================================
# 3. DATABASE LOKAL (CSV) — TULIS ATOMIK + KUNCI ANTAR-PENGGUNA
# =====================================================================
@st.cache_resource(show_spinner=False)
def _kunci_db() -> threading.RLock:
    """Satu kunci untuk semua sesi (semua HP surveyor) dalam satu server Streamlit."""
    return threading.RLock()


def _df_kosong() -> pd.DataFrame:
    return pd.DataFrame({k: pd.Series(dtype=str) for k in KOLOM_DB})


def _rapikan_skema(df: pd.DataFrame) -> pd.DataFrame:
    for k in KOLOM_DB:
        if k not in df.columns:
            df[k] = ""
    tambahan = [c for c in df.columns if c not in KOLOM_DB]
    return df[KOLOM_DB + tambahan].fillna("").astype(str)


def muat_db() -> pd.DataFrame:
    """Selalu baca ulang dari disk → status terbaru dari surveyor lain ikut tampil."""
    if not DB_PATH.exists():
        return _df_kosong()
    with _kunci_db():
        try:
            df = pd.read_csv(DB_PATH, dtype=str, keep_default_na=False, encoding="utf-8-sig")
        except pd.errors.EmptyDataError:
            return _df_kosong()
    return _rapikan_skema(df)


def _tulis_atomik(df: pd.DataFrame) -> None:
    """Tulis ke file sementara lalu os.replace → file CSV tidak pernah setengah-tertulis."""
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    fd, tmp = tempfile.mkstemp(prefix=".tmp_laka_", suffix=".csv", dir=str(DB_PATH.parent))
    try:
        with os.fdopen(fd, "w", encoding="utf-8-sig", newline="") as f:
            df.to_csv(f, index=False)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, DB_PATH)
    finally:
        if os.path.exists(tmp):
            os.remove(tmp)


def tambah_rekaman(rekaman: list[dict]) -> int:
    if not rekaman:
        return 0
    with _kunci_db():
        df = muat_db()
        sudah_ada = set(df["id"])
        baru = [r for r in rekaman if r["id"] not in sudah_ada]
        if baru:
            _tulis_atomik(_rapikan_skema(pd.concat([df, pd.DataFrame(baru)], ignore_index=True)))
    return len(baru)


def ubah_status(id_lp: str, status: str, surveyor: str = "", koordinat: tuple | None = None) -> bool:
    """Baca-ubah-tulis di dalam kunci: aman walau beberapa surveyor menandai bersamaan."""
    with _kunci_db():
        df = muat_db()
        cocok = df["id"] == id_lp
        if not cocok.any():
            return False
        df.loc[cocok, "status"] = status
        if status == STATUS_SUDAH:
            df.loc[cocok, ["waktu_survei", "surveyor"]] = [waktu_str(), rapikan_spasi(surveyor)]
            if koordinat:
                df.loc[cocok, ["lat", "lon", "akurasi_lokasi"]] = [
                    f"{koordinat[0]:.6f}", f"{koordinat[1]:.6f}", AKURASI_GPS]
        else:
            df.loc[cocok, ["waktu_survei", "surveyor"]] = ["", ""]
        _tulis_atomik(df)
    return True


def perbarui_lokasi(hasil: dict[str, dict]) -> None:
    if not hasil:
        return
    with _kunci_db():
        df = muat_db()
        for id_lp, h in hasil.items():
            cocok = (df["id"] == id_lp) & (df["akurasi_lokasi"] != AKURASI_GPS)  # titik GPS tak ditimpa
            df.loc[cocok, ["lat", "lon", "akurasi_lokasi"]] = [h["lat"], h["lon"], h["akurasi_lokasi"]]
        _tulis_atomik(df)


def gabungkan_backup(df_backup: pd.DataFrame) -> tuple[int, int]:
    """Pulihkan dari backup tanpa menimpa data baru: LP baru ditambahkan, status 'Sudah'
    dari backup dipertahankan, koordinat yang kosong diisi dari backup."""
    df_backup = _rapikan_skema(df_backup)
    df_backup = df_backup[df_backup["id"].str.len() > 0].drop_duplicates("id", keep="last")
    with _kunci_db():
        df = muat_db()
        idx = {v: i for i, v in enumerate(df["id"])}
        tambah, perbarui = [], 0
        for _, b in df_backup.iterrows():
            if b["id"] not in idx:
                tambah.append(b.to_dict())
                continue
            i = df.index[idx[b["id"]]]
            berubah = False
            if b["status"] == STATUS_SUDAH and df.at[i, "status"] != STATUS_SUDAH:
                for k in ("status", "waktu_survei", "surveyor"):
                    df.at[i, k] = b[k]
                berubah = True
            if b["lat"] and (not df.at[i, "lat"] or b["akurasi_lokasi"] == AKURASI_GPS):
                for k in ("lat", "lon", "akurasi_lokasi"):
                    df.at[i, k] = b[k]
                berubah = True
            perbarui += int(berubah)
        if tambah:
            df = pd.concat([df, pd.DataFrame(tambah)], ignore_index=True)
        _tulis_atomik(_rapikan_skema(df))
    return len(tambah), perbarui


# =====================================================================
# 4. GEOCODING BERLAPIS (ANTI NYASAR)
# =====================================================================
@st.cache_resource(show_spinner=False)
def _geocoder() -> RateLimiter:
    nominatim = Nominatim(user_agent=NOMINATIM_USER_AGENT, timeout=10)
    return RateLimiter(nominatim.geocode, min_delay_seconds=JEDA_GEOCODE_DETIK, max_retries=2,
                       error_wait_seconds=3.0, swallow_exceptions=False)


@st.cache_data(show_spinner=False, ttl=60 * 60 * 24 * 7, max_entries=5000)
def cari_lokasi(kueri: str) -> tuple[float, float, str] | None:
    """Satu kueri ke Nominatim (dibatasi Indonesia). Hasil di-cache 7 hari."""
    hasil = _geocoder()(kueri, country_codes="id", language="id", exactly_one=True)
    if hasil is None:
        return None
    return float(hasil.latitude), float(hasil.longitude), str(hasil.address)


def _norm_wilayah(s: str) -> str:
    s = re.sub(r"\b(?:kabupaten|kab|kota|kotamadya|provinsi)\b\.?", " ", (s or "").lower())
    return re.sub(r"[^a-z]", "", s)


def susun_kueri_geocode(rek: dict, wilayah: str = "") -> list[tuple[str, str]]:
    """Daftar (level, kueri) dari paling presisi → paling umum."""
    j, d, k, kb = (rapikan_spasi(rek.get(x, "")) for x in ("jalan", "desa", "kecamatan", "kabupaten"))
    konteks = kb or rapikan_spasi(wilayah)

    def gabung(*bagian: str) -> str:
        return ", ".join(b for b in bagian if b)

    kueri: list[tuple[str, str]] = []
    # Level 1 — alamat TKP lengkap (versi komponen bersih, lalu versi teks asli yang dirapikan)
    if sum(bool(x) for x in (j, d, k)) >= 2 or (j and konteks):
        kueri.append(("Alamat lengkap", gabung(j, d, k, konteks)))
    mentah = alamat_untuk_geocode(rek.get("alamat_tkp", ""))
    if mentah:
        if konteks and _norm_wilayah(konteks) not in _norm_wilayah(mentah):
            mentah = gabung(mentah, konteks)
        kueri.append(("Alamat lengkap", mentah))
    # Level 2 — Nama Jalan + Kecamatan
    if j and k:
        kueri.append(("Jalan + Kecamatan", gabung(j, k, konteks)))
        kueri.append(("Jalan + Kecamatan", gabung(j, k)))
    # Level 3 — Desa + Kecamatan (tambahan: jauh lebih presisi daripada titik tengah kecamatan)
    if d and k:
        kueri.append(("Desa + Kecamatan", gabung(d, k, konteks)))
        kueri.append(("Desa + Kecamatan", gabung(d, k)))
    # Level 4 — Kecamatan + Kabupaten
    if k and konteks:
        kueri.append(("Kecamatan + Kabupaten", gabung(k, konteks)))
    unik, terlihat = [], set()
    for level, q in kueri:
        if q and q.lower() not in terlihat:
            terlihat.add(q.lower())
            unik.append((level, q))
    return unik


def _hasil_di_wilayah(alamat_hasil: str, kabupaten: str, wilayah: str) -> bool:
    """Tolak hasil yang jatuh di kabupaten lain (nama jalan/desa banyak yang kembar)."""
    hasil = _norm_wilayah(alamat_hasil)
    if kabupaten:
        return _norm_wilayah(kabupaten) in hasil
    bagian = [_norm_wilayah(p) for p in (wilayah or "").split(",") if _norm_wilayah(p)]
    return not bagian or any(p in hasil for p in bagian)


def geocode_berlapis(rek: dict, wilayah: str = "", cari=None) -> dict:
    cari = cari or cari_lokasi
    for level, kueri in susun_kueri_geocode(rek, wilayah):
        try:
            hasil = cari(kueri)
        except (GeopyError, OSError, ValueError) as e:  # layanan sibuk / koneksi putus
            return {"lat": "", "lon": "", "akurasi_lokasi": AKURASI_TERTUNDA, "error": type(e).__name__}
        if hasil and _hasil_di_wilayah(hasil[2], rek.get("kabupaten", ""), wilayah):
            return {"lat": f"{hasil[0]:.6f}", "lon": f"{hasil[1]:.6f}", "akurasi_lokasi": level}
    return {"lat": "", "lon": "", "akurasi_lokasi": AKURASI_GAGAL}


def jalankan_geocoding(ids: list[str], wilayah: str = "", progres=None, cari=None) -> dict:
    """Geocode banyak LP; simpan per 5 LP agar aman jika proses terputus."""
    df = muat_db()
    target = df[df["id"].isin(ids) & (df["akurasi_lokasi"] != AKURASI_GPS)]
    rekap = {"ditemukan": 0, "tidak_ditemukan": 0, "tertunda": 0}
    antre: dict[str, dict] = {}
    error_beruntun = 0
    for n, (_, row) in enumerate(target.iterrows(), start=1):
        if error_beruntun >= 3:  # layanan sedang bermasalah → tunda sisanya, jangan dibombardir
            hasil = {"lat": "", "lon": "", "akurasi_lokasi": AKURASI_TERTUNDA}
        else:
            hasil = geocode_berlapis(row.to_dict(), wilayah, cari=cari)
            error_beruntun = error_beruntun + 1 if hasil["akurasi_lokasi"] == AKURASI_TERTUNDA else 0
        kunci = {AKURASI_GAGAL: "tidak_ditemukan", AKURASI_TERTUNDA: "tertunda"}.get(hasil["akurasi_lokasi"], "ditemukan")
        rekap[kunci] += 1
        antre[row["id"]] = hasil
        if len(antre) >= 5:
            perbarui_lokasi(antre)
            antre = {}
        if progres:
            progres(n, len(target), row)
    perbarui_lokasi(antre)
    return rekap


def proses_pdf(berkas: list, df_lama: pd.DataFrame, progres=None) -> tuple[list[dict], dict]:
    """Ekstrak semua PDF terunggah → daftar rekaman baru + laporan proses."""
    hash_lama, id_lama = set(df_lama["file_hash"]), set(df_lama["id"])
    laporan = {"duplikat": 0, "scan": [], "gagal": [], "kurang": []}
    rekaman: list[dict] = []
    id_baru: set[str] = set()
    for i, f in enumerate(berkas, start=1):
        data = f.getvalue()
        fh = hashlib.md5(data).hexdigest()
        if fh in hash_lama:
            laporan["duplikat"] += 1
        else:
            try:
                halaman = baca_halaman_pdf(data)
            except Exception as e:  # PDF rusak / terkunci password
                laporan["gagal"].append(f"{f.name} ({type(e).__name__})")
                halaman = None
            if halaman is None:
                pass
            elif sum(len(h.strip()) for h in halaman) < 40:
                laporan["scan"].append(f.name)  # PDF hasil scan (gambar) → perlu OCR
            else:
                for urutan, teks in enumerate(pecah_dokumen_lp(halaman)):
                    rek = ekstrak_lp(teks)
                    rek["id"] = buat_id(rek["nomor_lp"], fh, urutan)
                    if rek["id"] in id_lama or rek["id"] in id_baru:
                        laporan["duplikat"] += 1
                        continue
                    id_baru.add(rek["id"])
                    rek.update(status=STATUS_BELUM, waktu_survei="", surveyor="", nama_file=f.name, file_hash=fh,
                               waktu_input=waktu_str(), lat="", lon="", akurasi_lokasi=AKURASI_BELUM,
                               catatan=catatan_kelengkapan(rek))
                    if rek["catatan"]:
                        laporan["kurang"].append(f"{f.name}: {rek['catatan']}")
                    rekaman.append(rek)
        if progres:
            progres(i, len(berkas), f.name)
    return rekaman, laporan


# =====================================================================
# 5. PENCARIAN, JARAK & NAVIGASI
# =====================================================================
def url_navigasi(alamat_asli: str) -> str:
    """Bypass Nominatim: teks ASLI dari LP langsung dicari oleh Google Maps di HP."""
    teks = rapikan_spasi(alamat_asli)
    return f"https://www.google.com/maps/search/?api=1&query={quote_plus(teks)}" if teks else ""


def jarak_km(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    """Jarak garis lurus (haversine)."""
    p1, p2 = math.radians(lat1), math.radians(lat2)
    a = math.sin((p2 - p1) / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(math.radians(lon2 - lon1) / 2) ** 2
    return 2 * 6371.0088 * math.asin(math.sqrt(a))


def tambah_jarak(df: pd.DataFrame, gps: dict | None) -> pd.DataFrame:
    df = df.copy()
    lat, lon = pd.to_numeric(df["lat"], errors="coerce"), pd.to_numeric(df["lon"], errors="coerce")
    if gps:
        df["_jarak"] = [jarak_km(gps["lat"], gps["lon"], a, b) if pd.notna(a) and pd.notna(b) else math.inf
                        for a, b in zip(lat, lon)]
    else:
        df["_jarak"] = math.inf
    return df


def _kunci_lp(s: str) -> str:
    return re.sub(r"[^A-Z0-9]", "", (s or "").upper())


def cari_lp(df: pd.DataFrame, kueri: str, batas: int = 10) -> pd.DataFrame:
    """Cari berdasarkan Nomor LP atau Nama Korban — toleran salah ketik (fuzzy)."""
    q = rapikan_spasi(kueri).upper()
    if len(q) < 3 or df.empty:
        return df.iloc[0:0]
    q_lp = _kunci_lp(q)
    token = [t for t in re.split(r"[^A-Z0-9]+", q) if t]
    hasil = []
    for idx, r in df.iterrows():
        nama, lp = r["nama_korban"].upper(), _kunci_lp(r["nomor_lp"])
        skor = 0.0
        if len(q_lp) >= 3 and q_lp in lp:
            skor = 1.0 if (len(q_lp) >= 6 or lp.startswith(q_lp)) else 0.9
        if q in nama:
            skor = max(skor, 1.0)
        elif token and all(t in nama for t in token):
            skor = max(skor, 0.93)
        else:
            for n in (x.strip() for x in nama.split(",")):
                if not n:
                    continue
                per_kata = max((SequenceMatcher(None, t, w).ratio() for t in token for w in n.split()), default=0.0)
                skor = max(skor, SequenceMatcher(None, q, n).ratio(), per_kata * (0.95 if len(token) == 1 else 0.85))
        if skor >= 0.78:
            hasil.append((skor, r["status"] == STATUS_SUDAH, idx))
    hasil.sort(key=lambda x: (-x[0], x[1]))
    return df.loc[[i for _, _, i in hasil[:batas]]]


def filter_status(df: pd.DataFrame, mode: str) -> pd.DataFrame:
    if mode == FILTER_BELUM:
        return df[df["status"] != STATUS_SUDAH]
    if mode == FILTER_SUDAH:
        return df[df["status"] == STATUS_SUDAH]
    return df


def buat_excel(df: pd.DataFrame) -> bytes:
    kolom = {
        "nomor_lp": "Nomor LP", "nama_korban": "Nama Korban", "alamat_tkp": "Alamat TKP", "kecamatan": "Kecamatan",
        "kabupaten": "Kabupaten/Kota", "tanggal_kejadian": "Tanggal Kejadian", "kondisi_korban": "Kondisi Korban",
        "status": "Status Survei", "waktu_survei": "Waktu Survei", "surveyor": "Surveyor", "lat": "Latitude",
        "lon": "Longitude", "akurasi_lokasi": "Akurasi Titik", "ringkasan": "Kesimpulan Kronologi",
        "nama_file": "File PDF",
    }
    buf = io.BytesIO()
    with pd.ExcelWriter(buf, engine="openpyxl") as w:
        df[list(kolom)].rename(columns=kolom).to_excel(w, index=False, sheet_name="Rekap LP")
        ws = w.sheets["Rekap LP"]
        for huruf, lebar in zip("ABCDEFGHIJKLMNO", [34, 26, 48, 16, 16, 14, 12, 15, 17, 16, 11, 11, 20, 70, 28]):
            ws.column_dimensions[huruf].width = lebar
        ws.freeze_panes = "A2"
        ws.auto_filter.ref = ws.dimensions
    return buf.getvalue()


# =====================================================================
# 6. PETA (FOLIUM + GOOGLE MAPS TILES + LIVE GPS)
# =====================================================================
class _PeredamErrorGPS(MacroElement):
    """Ganti alert() bawaan LocateControl saat izin GPS ditolak → cukup console.warn,
    supaya HP tidak dihujani pop-up setiap kali peta dimuat ulang."""

    _template = Template("""
        {% macro script(this, kwargs) %}
            {{ this.kontrol.get_name() }}.options.onLocationError = function (e) {
                console.warn("GPS tidak tersedia:", e && e.message);
            };
        {% endmacro %}
    """)

    def __init__(self, kontrol: LocateControl):
        super().__init__()
        self._name = "PeredamErrorGPS"
        self.kontrol = kontrol


def html_popup(r) -> str:
    """Popup minimalis: HANYA Nomor LP, Nama Korban, Alamat TKP + tombol navigasi."""
    nav = url_navigasi(r["alamat_tkp"])
    tombol = (f'<a href="{esc(nav)}" target="_blank" rel="noopener" style="display:block;margin-top:8px;'
              'padding:9px 10px;background:#1a73e8;color:#fff;text-align:center;border-radius:8px;'
              'text-decoration:none;font-weight:600">🧭 Mulai Navigasi</a>') if nav else ""
    return (
        '<div style="font-family:system-ui,-apple-system,Segoe UI,Roboto,sans-serif;font-size:13px;'
        'line-height:1.35;min-width:190px;max-width:240px">'
        f'<div style="font-weight:700;font-size:12px;color:#334155;word-break:break-word">{esc(r["nomor_lp"] or "Nomor LP tidak terbaca")}</div>'
        f'<div style="margin-top:4px">👤 <b>{esc(r["nama_korban"] or "-")}</b></div>'
        f'<div style="margin-top:4px;color:#475569">📍 {esc(r["alamat_tkp"] or "-")}</div>'
        f"{tombol}</div>"
    )


def buat_peta(df_tampil: pd.DataFrame, mode: str, gps: dict | None = None, heatmap: bool = False) -> folium.Map:
    titik = df_tampil.assign(
        _lat=pd.to_numeric(df_tampil["lat"], errors="coerce"),
        _lon=pd.to_numeric(df_tampil["lon"], errors="coerce"),
    ).dropna(subset=["_lat", "_lon"])

    # Fokus tampilan: mode "Belum" + GPS → posisi Anda + 5 TKP terdekat; selain itu → semua titik
    pusat, zoom, batas = list(DEFAULT_CENTER), 5, None
    if not titik.empty:
        fokus = tambah_jarak(titik, gps).nsmallest(5, "_jarak") if (mode == FILTER_BELUM and gps) else titik
        lat, lon = list(fokus["_lat"]), list(fokus["_lon"])
        if mode == FILTER_BELUM and gps:
            lat.append(gps["lat"])
            lon.append(gps["lon"])
        if len(lat) == 1:
            pusat, zoom = [lat[0], lon[0]], 15
        else:
            pusat, zoom = [sum(lat) / len(lat), sum(lon) / len(lon)], 12
            batas = [[min(lat), min(lon)], [max(lat), max(lon)]]
    elif gps:
        pusat, zoom = [gps["lat"], gps["lon"]], 14

    m = folium.Map(location=pusat, zoom_start=zoom, tiles=None, control_scale=True)
    if batas:
        m.fit_bounds(batas, padding=(30, 30), max_zoom=16)
    folium.TileLayer(GOOGLE_TILE_JALAN, attr="Google Maps", name="Google Maps", max_zoom=21).add_to(m)
    folium.TileLayer(GOOGLE_TILE_SATELIT, attr="Google Maps", name="Satelit (Hybrid)", max_zoom=21,
                     show=False).add_to(m)

    klaster = MarkerCluster(name="Titik TKP", control=False, show_coverage_on_hover=False,
                            spiderfy_on_max_zoom=True, max_cluster_radius=45).add_to(m)
    for _, r in titik.iterrows():
        sudah = r["status"] == STATUS_SUDAH
        perkiraan = r["akurasi_lokasi"] in AKURASI_PERKIRAAN
        ikon = "question" if perkiraan else ("check" if sudah else "car")
        folium.Marker(
            location=[r["_lat"], r["_lon"]],
            popup=folium.Popup(html_popup(r), max_width=260),
            icon=folium.Icon(color="green" if sudah else "red", icon=ikon, prefix="fa"),
        ).add_to(klaster)

    if heatmap and not titik.empty:
        HeatMap(titik[["_lat", "_lon"]].values.tolist(), name="Heatmap titik rawan", radius=18, blur=15,
                min_opacity=0.35, max_zoom=15).add_to(m)

    # Live GPS di peta: titik biru + lingkar akurasi yang terus mengikuti posisi HP
    gps_ctrl = LocateControl(
        auto_start=True, position="topleft", flyTo=True, setView="once", showPopup=False,
        drawCircle=True, keepCurrentZoomLevel=False,
        clickBehavior={"inView": "setView", "outOfView": "setView", "inViewNotFollowing": "setView"},
        strings={"title": "Ke lokasi saya"},
        locateOptions={"enableHighAccuracy": True, "watch": True, "maxZoom": 17},
    )
    gps_ctrl.add_to(m)
    _PeredamErrorGPS(gps_ctrl).add_to(m)
    Fullscreen(position="topleft", title="Layar penuh", title_cancel="Keluar layar penuh").add_to(m)
    folium.LayerControl(position="topright", collapsed=True).add_to(m)
    return m


# =====================================================================
# 7. KOMPONEN UI (MOBILE-FIRST)
# =====================================================================
CSS = """
<style>
[data-testid="stMainBlockContainer"]{padding-top:2.4rem;padding-bottom:5rem;max-width:780px}
@media (max-width:640px){[data-testid="stMainBlockContainer"]{padding-left:.75rem;padding-right:.75rem;padding-top:1.8rem}}
[data-testid="stBaseButton-primary"],[data-testid="stBaseButton-secondary"],
[data-testid="stBaseLinkButton-primary"],[data-testid="stBaseLinkButton-secondary"]{min-height:46px;border-radius:12px;font-weight:600}
.jr-judul{font-size:1.32rem;font-weight:800;line-height:1.2;margin:0}
.jr-sub{opacity:.7;font-size:.82rem;margin:.1rem 0 .5rem}
.jr-stats{display:flex;gap:.45rem;margin:.2rem 0 .35rem}
.jr-stat{flex:1;min-width:0;border-radius:12px;padding:.45rem .3rem;text-align:center;border:1px solid rgba(128,128,128,.22)}
.jr-stat b{display:block;font-size:1.25rem;line-height:1.15}
.jr-stat span{font-size:.7rem;opacity:.8}
.jr-merah{background:rgba(220,38,38,.10)}.jr-hijau{background:rgba(22,163,74,.12)}
.jr-biru{background:rgba(37,99,235,.10)}.jr-abu{background:rgba(100,116,139,.10)}
.jr-badge{display:inline-block;font-size:.68rem;font-weight:700;padding:.12rem .55rem;border-radius:999px;margin:0 .25rem .3rem 0;letter-spacing:.02em}
.jr-b-belum{background:rgba(220,38,38,.14);color:#dc2626}.jr-b-sudah{background:rgba(22,163,74,.16);color:#16a34a}
.jr-b-md{background:rgba(15,23,42,.85);color:#fff}.jr-b-lb{background:rgba(234,88,12,.16);color:#ea580c}
.jr-b-lr{background:rgba(202,138,4,.18);color:#a16207}.jr-b-info{background:rgba(37,99,235,.12);color:#2563eb}
.jr-lp{font-weight:800;font-size:.88rem;word-break:break-word}
.jr-baris{margin-top:.28rem;font-size:.95rem;line-height:1.35}
.jr-redup{opacity:.72;font-size:.8rem}
.jr-kronologi{margin-top:.5rem;font-size:.88rem;line-height:1.45;padding:.5rem .65rem;border-left:3px solid rgba(37,99,235,.65);background:rgba(37,99,235,.06);border-radius:6px}
.jr-peringatan{margin-top:.4rem;font-size:.78rem;color:#b45309}
.jr-uraian{font-size:.9rem;line-height:1.5}
</style>
"""

JS_GPS = """new Promise((resolve) => {
  if (!navigator.geolocation) { resolve({error: {code: 0, message: "Browser tidak mendukung GPS"}}); return; }
  navigator.geolocation.getCurrentPosition(
    (p) => resolve({lat: p.coords.latitude, lon: p.coords.longitude, akurasi: p.coords.accuracy, waktu: p.timestamp}),
    (e) => resolve({error: {code: e.code, message: e.message}}),
    {enableHighAccuracy: true, timeout: 20000, maximumAge: 15000}
  );
})"""


def init_state() -> None:
    ss = st.session_state
    for kunci in ("gps_nonce", "uploader_nonce", "restore_nonce"):
        ss.setdefault(kunci, 0)


def _perbarui_gps() -> None:
    st.session_state.gps_nonce += 1


def _pilih_lp(nilai: str) -> None:
    st.session_state.cari = nilai  # kolom cari terikat ke URL → ikut tersimpan saat refresh


def komponen_gps() -> dict | None:
    """Ambil koordinat HP sekali per permintaan (untuk jarak & urutan TKP terdekat)."""
    ss = st.session_state
    if streamlit_js_eval is None:
        return None
    nilai = streamlit_js_eval(js_expressions=JS_GPS, key=f"gps_{ss.gps_nonce}")
    if isinstance(nilai, dict):
        if nilai.get("lat") is not None and nilai.get("lon") is not None:
            waktu = datetime.fromtimestamp(float(nilai.get("waktu") or 0) / 1000, WIB) if nilai.get("waktu") \
                else sekarang_wib()
            ss.gps = {"lat": float(nilai["lat"]), "lon": float(nilai["lon"]),
                      "akurasi": float(nilai.get("akurasi") or 0), "waktu": waktu.strftime("%H:%M")}
            ss.pop("gps_error", None)
        elif isinstance(nilai.get("error"), dict):
            ss.gps_error = nilai["error"].get("message") or "Izin lokasi ditolak"
    return ss.get("gps")


def strip_statistik(isi: list[tuple[str, str, str]]) -> str:
    kotak = "".join(f'<div class="jr-stat {kls}"><b>{esc(nilai)}</b><span>{esc(label)}</span></div>'
                    for nilai, label, kls in isi)
    return f'<div class="jr-stats">{kotak}</div>'


def render_header(df: pd.DataFrame) -> None:
    total = len(df)
    sudah = int((df["status"] == STATUS_SUDAH).sum())
    belum = total - sudah
    st.markdown('<p class="jr-judul">🚑 Survei TKP Laka Lantas</p>'
                '<p class="jr-sub">Jasa Raharja · Navigasi survei &amp; monitoring LP</p>', unsafe_allow_html=True)
    st.markdown(strip_statistik([
        (str(total), "Total LP", "jr-biru"), (str(belum), "Belum", "jr-merah"),
        (str(sudah), "Sudah", "jr-hijau"), (f"{(sudah / total if total else 0):.0%}", "Progres", "jr-abu"),
    ]), unsafe_allow_html=True)
    if total:
        st.progress(sudah / total)


def html_kartu(r, ringkas: bool = False) -> str:
    sudah = r["status"] == STATUS_SUDAH
    lencana = [f'<span class="jr-badge {"jr-b-sudah" if sudah else "jr-b-belum"}">'
               f'{"✅ SUDAH DISURVEI" if sudah else "⏳ BELUM DISURVEI"}</span>']
    if r["kondisi_korban"] in KONDISI_LABEL:
        lencana.append(f'<span class="jr-badge jr-b-{r["kondisi_korban"].lower()}">'
                       f'{esc(KONDISI_LABEL[r["kondisi_korban"]])}</span>')
    jarak = r.get("_jarak", math.inf)
    if isinstance(jarak, float) and math.isfinite(jarak):
        teks_jarak = f"{jarak * 1000:.0f} m" if jarak < 1 else f"{jarak:.1f} km".replace(".", ",")
        lencana.append(f'<span class="jr-badge jr-b-info">📏 ±{teks_jarak} dari Anda</span>')
    detail = []
    if r["tanggal_kejadian"]:
        detail.append(f"🗓️ {esc(r['tanggal_kejadian'])}")
    detail.append(f"🎯 Titik peta: {esc(r['akurasi_lokasi'] or AKURASI_BELUM)}")
    bagian = [
        "".join(lencana),
        f'<div class="jr-lp">{esc(r["nomor_lp"] or "Nomor LP tidak terbaca")}</div>',
        f'<div class="jr-baris">👤 <b>{esc(r["nama_korban"] or "Nama korban tidak terbaca")}</b></div>',
        f'<div class="jr-baris">📍 {esc(r["alamat_tkp"] or "Alamat TKP tidak terbaca")}</div>',
        f'<div class="jr-baris jr-redup">{" · ".join(detail)}</div>',
    ]
    if not ringkas:
        kronologi = r["ringkasan"] or r["uraian"]
        bagian.append(f'<div class="jr-kronologi"><b>Kesimpulan laka:</b> '
                      f'{esc(kronologi or "Uraian tidak ditemukan di PDF.")}</div>')
        if sudah:
            bagian.append(f'<div class="jr-baris jr-redup">✅ Disurvei {esc(r["waktu_survei"])}'
                          f'{" oleh " + esc(r["surveyor"]) if r["surveyor"] else ""}</div>')
        if r["catatan"]:
            bagian.append(f'<div class="jr-peringatan">⚠️ {esc(r["catatan"])} — cek PDF asli.</div>')
    return "".join(bagian)


def render_kartu(r, gps: dict | None, konteks: str, ringkas: bool = False) -> None:
    """Kartu detail LP (pengganti tabel lebar, nyaman di layar HP)."""
    id_lp = r["id"]
    sudah = r["status"] == STATUS_SUDAH
    nav = url_navigasi(r["alamat_tkp"])
    with st.container(border=True, key=f"kartu_{konteks}_{id_lp}"):
        st.markdown(html_kartu(r, ringkas), unsafe_allow_html=True)
        if ringkas:
            kiri, kanan = st.columns(2)
            with kiri:
                if nav:
                    st.link_button("🧭 Navigasi", nav, type="primary", width="stretch")
            with kanan:
                st.button("🔎 Detail", key=f"detail_{konteks}_{id_lp}", on_click=_pilih_lp,
                          args=(r["nomor_lp"] or r["nama_korban"],), width="stretch")
            return
        if r["uraian"] and r["uraian"] != r["ringkasan"]:
            with st.expander("📄 Uraian lengkap LP"):
                st.markdown(f'<div class="jr-uraian">{esc(r["uraian"])}</div>', unsafe_allow_html=True)
        if nav:
            st.link_button("🧭 Mulai Navigasi", nav, width="stretch")
        else:
            st.button("🧭 Alamat TKP tidak tersedia", key=f"nonav_{konteks}_{id_lp}", disabled=True,
                      width="stretch")
        if not sudah:
            simpan_gps = st.checkbox(
                "📍 Simpan posisi GPS saya sebagai titik TKP", key=f"simpan_gps_{konteks}_{id_lp}",
                disabled=gps is None,
                help="Centang hanya jika Anda sedang berdiri di TKP. Titik peta LP ini akan dikoreksi "
                     "dengan GPS HP (paling akurat untuk monitoring).")
            if st.button("✅ Tandai Sudah Disurvei", key=f"tandai_{konteks}_{id_lp}", type="primary",
                         width="stretch"):
                koordinat = (gps["lat"], gps["lon"]) if (simpan_gps and gps) else None
                if ubah_status(id_lp, STATUS_SUDAH, st.session_state.get("surveyor", ""), koordinat):
                    st.session_state.pesan = f"✅ {r['nomor_lp'] or r['nama_korban']} ditandai Sudah Disurvei"
                else:
                    st.session_state.pesan = "⚠️ LP tidak ditemukan di database (mungkin sudah dihapus)."
                st.rerun()
        elif st.button("↩️ Batalkan status (kembali ke Belum)", key=f"batal_{konteks}_{id_lp}", width="stretch"):
            ubah_status(id_lp, STATUS_BELUM)
            st.session_state.pesan = f"↩️ {r['nomor_lp'] or r['nama_korban']} dikembalikan ke Belum Disurvei"
            st.rerun()


@st.fragment
def bagian_pencarian() -> None:
    """Fragment: mengetik di kolom cari hanya me-rerun bagian ini, peta tidak dimuat ulang."""
    st.markdown("##### 🔎 Sudah di lokasi? Cari LP-nya")
    kueri = st.text_input(
        "Cari Nomor LP atau Nama Korban", key="cari", type="search", live=True, bind="query-params",
        placeholder="ketik nama korban atau nomor LP…", label_visibility="collapsed")
    df = muat_db()  # selalu data terbaru
    gps = st.session_state.get("gps")
    q = rapikan_spasi(kueri or "")
    if q:
        if len(q) < 3:
            st.caption("Ketik minimal 3 huruf/angka.")
            return
        hasil = tambah_jarak(cari_lp(df, q), gps)
        if hasil.empty:
            st.warning("LP tidak ditemukan. Coba sebagian nama saja (mis. 3–5 huruf) atau angka nomor LP.")
            return
        st.caption(f"{len(hasil)} hasil · mencari di semua LP (belum & sudah disurvei)")
        for _, r in hasil.iterrows():
            render_kartu(r, gps, "cari")
        return
    belum = df[df["status"] != STATUS_SUDAH]
    if belum.empty:
        return
    daftar = tambah_jarak(belum, gps)
    if gps:
        daftar = daftar.sort_values("_jarak", kind="stable")
        judul = "📋 5 TKP terdekat yang belum disurvei"
    else:
        daftar = daftar.sort_values("waktu_input", ascending=False, kind="stable")
        judul = "📋 5 LP terbaru yang belum disurvei"
    with st.expander(judul):
        for _, r in daftar.head(5).iterrows():
            render_kartu(r, gps, "daftar", ringkas=True)


def render_peta(df_mode: pd.DataFrame, mode: str, gps: dict | None) -> None:
    heatmap = mode == FILTER_SEMUA and st.toggle("🔥 Heatmap titik rawan laka", key="heatmap")
    st_folium(buat_peta(df_mode, mode, gps, heatmap), key="peta_tkp", height=430,
              use_container_width=True, returned_objects=[])
    tanpa_titik = int((pd.to_numeric(df_mode["lat"], errors="coerce").isna()).sum())
    keterangan = "🔴 Belum · 🟢 Sudah · ❓ titik perkiraan (tingkat desa/kecamatan)"
    if tanpa_titik:
        keterangan += f" · {tanpa_titik} LP belum punya titik (tetap bisa dicari di bawah)"
    kiri, kanan = st.columns([3, 2], vertical_alignment="center")
    with kiri:
        ss = st.session_state
        if gps:
            st.caption(f"{keterangan}  \n📡 GPS ±{gps['akurasi']:.0f} m · {gps['waktu']} WIB")
        elif ss.get("gps_error"):
            st.caption(f"{keterangan}  \n⚠️ GPS: {ss.gps_error}. Izinkan akses lokasi untuk situs ini di Chrome.")
        elif streamlit_js_eval is None:
            st.caption(f"{keterangan}  \nℹ️ Paket streamlit-js-eval tidak terpasang: urutan jarak nonaktif.")
        else:
            st.caption(f"{keterangan}  \n📡 Menunggu izin/sinyal GPS…")
    with kanan:
        st.button("📍 Perbarui GPS", on_click=_perbarui_gps, width="stretch",
                  disabled=streamlit_js_eval is None)


def render_monitoring(df: pd.DataFrame) -> None:
    st.markdown("##### 📊 Monitoring Angka Laka")
    kondisi = df["kondisi_korban"].value_counts()
    tanpa_titik = int(pd.to_numeric(df["lat"], errors="coerce").isna().sum())
    perkiraan = int(df["akurasi_lokasi"].isin(AKURASI_PERKIRAAN).sum())
    st.markdown(strip_statistik([
        (str(int(kondisi.get("MD", 0))), "Meninggal", "jr-abu"), (str(int(kondisi.get("LB", 0))), "Luka berat", "jr-merah"),
        (str(int(kondisi.get("LR", 0))), "Luka ringan", "jr-biru"), (str(tanpa_titik + perkiraan), "Titik perlu cek", "jr-hijau"),
    ]), unsafe_allow_html=True)
    kec = df["kecamatan"].replace("", "(tidak terbaca)").value_counts().head(10)
    if not kec.empty:
        st.caption("10 kecamatan dengan LP terbanyak")
        data_kec = kec.rename_axis("Kecamatan").reset_index(name="Jumlah LP")
        st.bar_chart(data_kec, x="Kecamatan", y="Jumlah LP", horizontal=True, sort="-Jumlah LP",
                     height=40 + 30 * len(data_kec))
    tanggal = pd.to_datetime(df["tanggal_kejadian"], errors="coerce").dropna()
    if not tanggal.empty:
        st.caption("Jumlah LP per bulan kejadian")
        per_bulan = tanggal.dt.strftime("%Y-%m").value_counts().sort_index()
        st.bar_chart(per_bulan.rename_axis("Bulan").reset_index(name="Jumlah LP"), x="Bulan", y="Jumlah LP",
                     height=240)
    st.download_button("⬇️ Unduh rekap Excel", data=buat_excel(df),
                       file_name=f"rekap_laka_{sekarang_wib():%Y%m%d_%H%M}.xlsx",
                       mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                       width="stretch")


def _tampilkan_laporan_proses() -> None:
    lap = st.session_state.get("laporan_proses")
    if not lap:
        return
    st.success(f"✅ {lap['baru']} LP baru · {lap['duplikat']} duplikat dilewati · "
               f"{lap['ditemukan']} titik ditemukan")
    if lap["tidak_ditemukan"] or lap["tertunda"]:
        st.warning(f"📍 {lap['tidak_ditemukan']} alamat tidak ditemukan, {lap['tertunda']} tertunda. "
                   "LP tetap bisa dicari & dinavigasi lewat teks alamat asli.")
    if lap["scan"]:
        st.warning("🖨️ PDF hasil scan (tanpa teks, perlu OCR): " + ", ".join(lap["scan"][:10]))
    if lap["gagal"]:
        st.error("❌ Gagal dibaca: " + ", ".join(lap["gagal"][:10]))
    if lap["kurang"]:
        with st.expander(f"⚠️ {len(lap['kurang'])} LP datanya belum lengkap"):
            st.markdown("\n".join(f"- {esc(x)}" for x in lap["kurang"][:50]))
    if st.button("Tutup laporan", key="tutup_laporan", width="stretch"):
        st.session_state.pop("laporan_proses", None)
        st.rerun()


def sidebar_admin(df: pd.DataFrame) -> None:
    ss = st.session_state
    st.markdown("### ⚙️ Panel Admin")
    st.text_input("👤 Nama surveyor", key="surveyor", bind="query-params",
                  placeholder="opsional — dicatat saat menandai survei")
    wilayah = st.text_input("🗺️ Wilayah kerja (opsional)", key="wilayah", bind="query-params",
                            placeholder="contoh: Blora, Jawa Tengah",
                            help="Dipakai saat alamat LP tidak menyebut kabupaten, agar titik tidak "
                                 "nyasar ke daerah lain yang nama jalannya sama.")

    with st.expander("📤 Upload LP (PDF)", expanded=df.empty):
        berkas = st.file_uploader("Pilih PDF Laporan Polisi (boleh ratusan sekaligus)", type=["pdf"],
                                  accept_multiple_files=True, key=f"unggah_{ss.uploader_nonce}")
        if st.button("⚙️ Ekstrak & Petakan", type="primary", disabled=not berkas, width="stretch"):
            with st.status("Memproses LP…", expanded=True) as status:
                bar = st.progress(0.0, text="Membaca PDF…")
                rekaman, laporan = proses_pdf(
                    berkas, muat_db(),
                    progres=lambda i, n, nama: bar.progress(i / n, text=f"Membaca PDF {i}/{n}: {nama}"))
                laporan["baru"] = tambah_rekaman(rekaman)
                bar.progress(0.0, text="Mencari koordinat TKP…")
                rekap = jalankan_geocoding(
                    [r["id"] for r in rekaman], wilayah,
                    progres=lambda i, n, row: bar.progress(i / n, text=f"Geocoding {i}/{n}: {row['nomor_lp'] or row['nama_file']}"))
                laporan.update(rekap)
                status.update(label="Selesai ✅", state="complete")
            ss.laporan_proses = laporan
            ss.uploader_nonce += 1  # kosongkan pemilih file agar tidak diproses ulang
            st.rerun()
        _tampilkan_laporan_proses()

    with st.expander("🛠️ Perawatan & backup data"):
        perlu = df[df["akurasi_lokasi"].isin(AKURASI_PERLU_ULANG)]
        if st.button(f"🔁 Cari ulang koordinat ({len(perlu)} LP)", disabled=perlu.empty, width="stretch"):
            bar = st.progress(0.0, text="Geocoding ulang…")
            rekap = jalankan_geocoding(list(perlu["id"]), wilayah,
                                       progres=lambda i, n, row: bar.progress(i / n, text=f"Geocoding {i}/{n}"))
            ss.pesan = (f"📍 {rekap['ditemukan']} titik ditemukan, {rekap['tidak_ditemukan']} tidak ditemukan, "
                        f"{rekap['tertunda']} tertunda")
            st.rerun()
        st.download_button("💾 Unduh backup database (CSV)", data=df.to_csv(index=False).encode("utf-8-sig"),
                           file_name=f"backup_database_laka_{sekarang_wib():%Y%m%d_%H%M}.csv", mime="text/csv",
                           disabled=df.empty, width="stretch")
        cadangan = st.file_uploader("♻️ Pulihkan dari file backup CSV", type=["csv"], key=f"pulih_{ss.restore_nonce}")
        if cadangan is not None and st.button("Gabungkan backup ke database", width="stretch"):
            try:  # sep=None: otomatis kenali pemisah "," atau ";" (CSV yang sempat dibuka-simpan di Excel)
                df_b = pd.read_csv(cadangan, dtype=str, keep_default_na=False, encoding="utf-8-sig",
                                   sep=None, engine="python")
            except Exception as e:
                st.error(f"File backup tidak bisa dibaca: {e}")
            else:
                if not {"id", "status"}.issubset(df_b.columns):
                    st.error("Ini bukan file backup aplikasi ini (kolom 'id' dan 'status' tidak ada).")
                else:
                    tambah, ubah = gabungkan_backup(df_b)
                    ss.pesan = f"♻️ Backup digabung: {tambah} LP ditambahkan, {ubah} LP diperbarui"
                    ss.restore_nonce += 1
                    st.rerun()

    with st.expander("🔬 Uji ekstraksi 1 PDF (tanpa menyimpan)"):
        uji = st.file_uploader("PDF contoh", type=["pdf"], key="uji_pdf")
        if uji is not None:
            try:
                halaman = baca_halaman_pdf(uji.getvalue())
            except Exception as e:
                st.error(f"PDF tidak bisa dibaca: {e}")
            else:
                segmen = pecah_dokumen_lp(halaman) if any(h.strip() for h in halaman) else []
                st.caption(f"{len(halaman)} halaman · {len(segmen)} dokumen LP terdeteksi")
                for teks in segmen:
                    st.json(ekstrak_lp(teks), expanded=True)
                st.text_area("Teks mentah hasil pdfplumber", "\n\n".join(halaman)[:8000], height=260)


# =====================================================================
# 8. HALAMAN UTAMA
# =====================================================================
def main() -> None:
    st.set_page_config(page_title="Survei TKP Laka · Jasa Raharja", page_icon="🚑", layout="centered",
                       initial_sidebar_state="collapsed")
    st.html(CSS)
    init_state()
    if st.session_state.get("pesan"):
        st.toast(st.session_state.pop("pesan"))
    try:
        df = muat_db()
    except Exception as e:  # jangan pernah menimpa CSV yang gagal dibaca
        st.error(f"Database `{DB_PATH.name}` tidak bisa dibaca ({e}). Perbaiki/pulihkan file tersebut dulu.")
        st.stop()

    with st.sidebar:
        gps = komponen_gps()  # komponen GPS tak terlihat (ditaruh di sidebar agar tidak makan tempat)
        sidebar_admin(df)

    render_header(df)
    if df.empty:
        st.info("Belum ada data LP. Buka **Panel Admin** (ikon **»** di kiri atas) → **Upload LP (PDF)**.")
    mode = st.radio("Filter peta", list(LABEL_FILTER), format_func=LABEL_FILTER.get, horizontal=True,
                    key="filter", bind="query-params", label_visibility="collapsed")
    render_peta(filter_status(df, mode), mode, gps)
    if not df.empty:
        bagian_pencarian()
        if mode == FILTER_SEMUA:
            render_monitoring(df)


if __name__ == "__main__":
    main()
