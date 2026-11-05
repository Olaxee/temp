#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
mpu_toolkit.py — Media Player Utilities Toolkit (un seul fichier, Python 3 + Tkinter)
=====================================================================================
Reconstruction fidèle de la logique de « Media Player Utilities 4.46 » (Actions Semiconductor) :
  * convertisseur « AMV/AVI Video Converter » (sortie .amv ou .avi MJPEG/ADPCM pour lecteurs MP3/MP4 à puce Actions) ;
  * lecteur AMV (décodeur identique au décodeur officiel AMV_DecDLL.dll) ;
  * outils : informations/vérification, export vers MP4, téléchargeur « MediaGet », copie vers le lecteur.

Ce qui est VALIDÉ octet par octet contre les DLL d'origine (exécutées sous Wine, voir TESTS_REELS.md) :
  encodeur AMV (vidéo, audio, conteneur), encodeur AVI (JPEG, ADPCM WAV, en-tête, index), décodeur AMV (vidéo + audio).
Ce qui est SUPPOSÉ ou choisi par cet outil (non vérifiable sans MFC42.DLL, cf. EXC-001) :
  options Insertwave/Insertpic, mode d'image (étirer/ratio/recadrer), gain ACOE, 16 bits (RGB565), interface graphique,
  téléchargeur, copie vers le lecteur, sélection des images par le filtre fps de ffmpeg.

Dépendances : Python >= 3.8, numpy, Tkinter (module standard), et les programmes ffmpeg + ffprobe (décodage des vidéos sources,
à la place de DirectShow / FFMpegDll). Aucune autre bibliothèque.

Utilisation :
    python mpu_toolkit.py                       # interface graphique
    python mpu_toolkit.py convert in.mp4 out.amv --size 160x120 --fps 30
    python mpu_toolkit.py convert in.mp4 out.avi --fmt avi --size 176x144 --fps 22
    python mpu_toolkit.py info fichier.amv      # propriétés + vérification de structure
    python mpu_toolkit.py export fichier.amv sortie.mp4
    python mpu_toolkit.py selftest              # auto-tests internes (tables, codecs, aller-retour)
"""
import os
import sys
import re
import json
import math
import math as _math
import time
import shutil
import queue
import struct as _struct
import threading
import tempfile
import subprocess
import configparser
import urllib.request
import urllib.parse
import urllib.error

try:
    import numpy as np
except ImportError:                                  # message clair plutôt qu'une trace
    sys.stderr.write("numpy est requis : pip install numpy\n")
    raise

APP_NAME = "Media Player Utilities Toolkit"
APP_VERSION = "1.0"
ORIGINAL_VERSION = "AMV/AVI Video Converter V4.46 (2012)"

# --------------------------------------------------------------------------------------------
# Spécifications relevées dans AmvTransform.ini ([Option]) du convertisseur d'origine
# --------------------------------------------------------------------------------------------
# format : (largeur, hauteur, (fps bas, fps moyen, fps haut))
AMV_SIZES = [
    (96, 64, (16, 25, 30)), (128, 96, (16, 25, 30)), (128, 128, (16, 25, 30)), (160, 120, (16, 25, 30)),
    (160, 128, (16, 25, 30)), (176, 128, (16, 25, 30)), (176, 144, (16, 25, 30)), (192, 160, (16, 25, 30)),
    (208, 120, (16, 25, 30)), (208, 160, (16, 25, 30)), (208, 176, (16, 25, 30)), (320, 240, (16, 20, 25)),
]
AVI_SIZES = [(w, h, (14, 22, 22)) for (w, h, _f) in AMV_SIZES]
AUDIO_RATES_AMV = (22050, 32000)          # option « fréquence audio » (index 0 / 1) de transdll @0x1c90
AVI_AUDIO_RATE = 22050                    # fixe en AVI
DEFAULT_SIZE_INDEX = 3                    # VWH=3 -> 160x120
DEFAULT_FPS_LEVEL = 2                     # VFBS=high
ORIENTATIONS = ("normal", "flipv", "fliph", "rot180", "rot90cw", "rot90ccw")   # UIInfo110
ASPECT_MODES = ("stretch", "letterbox", "crop")                                   # stretch = comportement mesuré de FFMpegDll
FFMPEG_ORIENT_FILTER = {
    "normal": "", "flipv": "vflip", "fliph": "hflip", "rot180": "hflip,vflip", "rot90cw": "transpose=1", "rot90ccw": "transpose=2",
}
VIDEO_EXTENSIONS = (".avi", ".mp4", ".mkv", ".mov", ".wmv", ".asf", ".flv", ".rm", ".rmvb", ".mpg", ".mpeg", ".vob", ".3gp", ".ts",
                    ".m4v", ".webm", ".swf", ".amv", ".divx", ".mts", ".m2ts")



# ============================================================================================
# CODEC AMV / AVI (reconstruit depuis AMV_EncDLL.dll, AVI_EncDLL.dll, AMV_DecDLL.dll — validé octet par octet)
# ============================================================================================


# --------------------------------------------------------------------------------------------
# Tables extraites de AMV_EncDLL.dll (RVA indiqués) — vérifiées bit à bit par les tests.
# --------------------------------------------------------------------------------------------
# Quantification (ordre naturel/raster, int16) : luma @0xe348, chroma @0xe3c8
QY = np.array([
    8, 6, 5, 8, 12, 20, 26, 31,   6, 6, 7, 10, 13, 29, 30, 28,   7, 7, 8, 12, 20, 29, 35, 28,   7, 9, 11, 15, 26, 44, 40, 31,
    9, 11, 19, 28, 34, 55, 52, 39,   12, 18, 28, 32, 41, 52, 57, 46,   25, 32, 39, 44, 52, 61, 60, 51,   36, 46, 48, 49, 56, 50, 52, 50], dtype=np.int64)
QC = np.array([
    9, 9, 12, 24, 50, 50, 50, 50,   9, 11, 13, 33, 50, 50, 50, 50,   12, 13, 28, 50, 50, 50, 50, 50,   24, 33, 50, 50, 50, 50, 50, 50] + [50] * 32, dtype=np.int64)
# Réciproques utilisés par le code d'origine : floor(65536/q)+1 (@0xe448 luma, @0xe548 chroma)
RY = (65536 // QY) + 1
RC = (65536 // QC) + 1
# Zigzag standard (positions 1..63) @0x110c4
ZIGZAG = [0, 1, 8, 16, 9, 2, 3, 10, 17, 24, 32, 25, 18, 11, 4, 5, 12, 19, 26, 33, 40, 48, 41, 34, 27, 20, 13, 6, 7, 14, 21, 28, 35, 42, 49, 56,
          57, 50, 43, 36, 29, 22, 15, 23, 30, 37, 44, 51, 58, 59, 52, 45, 38, 31, 39, 46, 53, 60, 61, 54, 47, 55, 62, 63]
# Masque « triangle » : le code d'origine force à 0 tout coefficient dont (ligne + colonne) >= 8 (0x2df0)
_idx = np.arange(64)
KEEP = ((_idx >> 3) + (_idx & 7)) < 8

# Huffman standard (Annexe K de la norme JPEG) — identiques aux tables de la DLL (@0xe648.. DC, @0xe6c0.. AC)
_DC_L_BITS = [0, 1, 5, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0]; _DC_L_VALS = list(range(12))
_DC_C_BITS = [0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0]; _DC_C_VALS = list(range(12))
_AC_L_BITS = [0, 2, 1, 3, 3, 2, 4, 3, 5, 5, 4, 4, 0, 0, 1, 0x7d]
_AC_L_VALS = [
    0x01, 0x02, 0x03, 0x00, 0x04, 0x11, 0x05, 0x12, 0x21, 0x31, 0x41, 0x06, 0x13, 0x51, 0x61, 0x07, 0x22, 0x71, 0x14, 0x32, 0x81, 0x91, 0xa1, 0x08,
    0x23, 0x42, 0xb1, 0xc1, 0x15, 0x52, 0xd1, 0xf0, 0x24, 0x33, 0x62, 0x72, 0x82, 0x09, 0x0a, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x25, 0x26, 0x27, 0x28,
    0x29, 0x2a, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59,
    0x5a, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89,
    0x8a, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6,
    0xb7, 0xb8, 0xb9, 0xba, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda, 0xe1, 0xe2,
    0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa]
_AC_C_BITS = [0, 2, 1, 2, 4, 4, 3, 4, 7, 5, 4, 4, 0, 1, 2, 0x77]
_AC_C_VALS = [
    0x00, 0x01, 0x02, 0x03, 0x11, 0x04, 0x05, 0x21, 0x31, 0x06, 0x12, 0x41, 0x51, 0x07, 0x61, 0x71, 0x13, 0x22, 0x32, 0x81, 0x08, 0x14, 0x42, 0x91,
    0xa1, 0xb1, 0xc1, 0x09, 0x23, 0x33, 0x52, 0xf0, 0x15, 0x62, 0x72, 0xd1, 0x0a, 0x16, 0x24, 0x34, 0xe1, 0x25, 0xf1, 0x17, 0x18, 0x19, 0x1a, 0x26,
    0x27, 0x28, 0x29, 0x2a, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,
    0x59, 0x5a, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
    0x88, 0x89, 0x8a, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xb2, 0xb3, 0xb4,
    0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda,
    0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa]


def _build_huff(bits, vals):
    """Retourne dict symbole -> (code, longueur) selon l'algorithme canonique JPEG (Annexe C)."""
    table = {}
    code = 0
    k = 0
    for length in range(1, 17):
        for _ in range(bits[length - 1]):
            table[vals[k]] = (code, length)
            code += 1
            k += 1
        code <<= 1
    return table


DC_HUFF = (_build_huff(_DC_L_BITS, _DC_L_VALS), _build_huff(_DC_C_BITS, _DC_C_VALS))
AC_HUFF = (_build_huff(_AC_L_BITS, _AC_L_VALS), _build_huff(_AC_C_BITS, _AC_C_VALS))

# Tables RGB->YCbCr (IJG, FIX 16 bits, décalage >>2 puis >>14 final) : reconstruction exacte de @0xf0c0 (8 x 256 int32)
_FIX = dict(R_Y=19595, G_Y=38470, B_Y=7471, R_CB=-11059, G_CB=-21709, B_CB=32768, R_CR=32768, G_CR=-27439, B_CR=-5329)
_I = np.arange(256, dtype=np.int64)
T_R_Y = (_FIX['R_Y'] * _I) >> 2
T_G_Y = (_FIX['G_Y'] * _I) >> 2
T_B_Y = ((_FIX['B_Y'] * _I) >> 2) + 8192
T_R_CB = (_FIX['R_CB'] * _I) >> 2
T_G_CB = (_FIX['G_CB'] * _I) >> 2
T_B_CB = ((_FIX['B_CB'] * _I) >> 2) + (128 << 14) + 8191
T_R_CR = T_B_CB.copy()
T_G_CR = (_FIX['G_CR'] * _I) >> 2
T_B_CR = (_FIX['B_CR'] * _I) >> 2
DLL_COLOR_TABLE_ORDER = [T_R_Y, T_G_Y, T_B_Y, T_R_CB, T_G_CB, T_B_CB, T_G_CR, T_B_CR]  # ordre @0xf0c0


# Hauteurs / largeurs gérées par AMV_EncDLL.dll (tables 0x2210 / 0x2310) ; au-delà : comportement indéfini côté DLL
DLL_ROWS_BY_HEIGHT = {600: 38, 768: 48, 480: 30, 960: 60, 96: 6, 64: 4, 288: 18, 144: 9, 240: 15, 120: 8, 128: 8, 160: 10}
DLL_COLS_BY_WIDTH = {320: 20, 208: 13, 192: 12, 176: 11, 160: 10, 128: 8}


def _fdct_1d(x):
    """Une passe de la DCT entière de la DLL (@0x27b0). x : liste de 8 tableaux (même forme). Retourne (y0..y7) AVANT arrondi final."""
    x0, x1, x2, x3, x4, x5, x6, x7 = x
    s07, d07 = x0 + x7, x0 - x7
    s16, d16 = x1 + x6, x1 - x6
    s25, d25 = x2 + x5, x2 - x5
    s34, d34 = x3 + x4, x3 - x4
    return s07, d07, s16, d16, s25, d25, s34, d34


def fdct_blocks(blocks):
    """DCT 8x8 de AMV_EncDLL (deux passes entières). blocks : int64 (N,8,8) déjà décalés de -128. Retourne int64 (N,8,8)."""
    b = blocks.astype(np.int64)
    # passe 1 : lignes (axe -1)
    s07, d07, s16, d16, s25, d25, s34, d34 = _fdct_1d([b[..., i] for i in range(8)])
    y = np.empty_like(b)
    y[..., 0] = 4 * (s07 + s16 + s25 + s34)
    y[..., 4] = 4 * (s07 - s16 - s25 + s34)
    y[..., 1] = (11363 * d07 + 9633 * d16 + 6437 * d25 + 2260 * d34 + 1024) >> 11
    y[..., 2] = (10703 * (s07 - s34) + 4433 * (s16 - s25) + 1024) >> 11
    y[..., 3] = (9633 * d07 - 11362 * d25 - 6436 * d34 - 2259 * d16 + 1024) >> 11
    y[..., 5] = (9633 * d34 - 11362 * d16 + 6437 * d07 + 2261 * d25 + 1024) >> 11
    y[..., 6] = (10704 * (s25 - s16) + 4433 * (s07 - s34) + 1024) >> 11
    y[..., 7] = (9633 * d25 - 11363 * d34 - 6436 * d16 + 2260 * d07 + 1024) >> 11
    # passe 2 : colonnes (axe -2)
    s07, d07, s16, d16, s25, d25, s34, d34 = _fdct_1d([y[..., i, :] for i in range(8)])
    z = np.empty_like(y)
    z[..., 0, :] = (s07 + s16 + s25 + s34 + 2) >> 2
    z[..., 4, :] = (s07 - s16 - s25 + s34 + 2) >> 2
    z[..., 1, :] = (11363 * d07 + 9633 * d16 + 6437 * d25 + 2260 * d34 + 16384) >> 15
    z[..., 2, :] = (10703 * (s07 - s34) + 4433 * (s16 - s25) + 16384) >> 15
    z[..., 3, :] = (9633 * d07 - 11362 * d25 - 6436 * d34 - 2259 * d16 + 16384) >> 15
    z[..., 5, :] = (9633 * d34 - 11362 * d16 + 6437 * d07 + 2261 * d25 + 16384) >> 15
    z[..., 6, :] = (10704 * (s25 - s16) + 4433 * (s07 - s34) + 16384) >> 15
    z[..., 7, :] = (9633 * d25 - 11363 * d34 - 6436 * d16 + 2260 * d07 + 16384) >> 15
    return z


def quantize_blocks(dct, luma, zero_triangle=True):
    """Quantification d'origine (@0x2df0) : arrondi au plus près via réciproque, puis zéro pour (ligne+colonne) >= 8."""
    q = QY if luma else QC
    r = RY if luma else RC
    c = dct.reshape(-1, 64).astype(np.int64)
    q8 = (q * 8)[None, :]
    half = q8 >> 1
    pos = c >= 0
    t = np.where(pos, c + half, half - c)
    mag = np.where(t < q8, 0, ((t >> 3) * r[None, :]) >> 16)
    out = np.where(pos, mag, -mag)
    if zero_triangle:
        out = np.where(KEEP[None, :], out, 0)
    return out


def rgb_to_ycc_planes(bgr_rows):
    """bgr_rows : uint8 (h, w, 3) en ordre mémoire (B,G,R). Retourne Y (h,w) int, Cb/Cr per-pixel (h,w) int (avant sous-échantillonnage)."""
    B = bgr_rows[..., 0].astype(np.int64)
    G = bgr_rows[..., 1].astype(np.int64)
    R = bgr_rows[..., 2].astype(np.int64)
    Y = (T_R_Y[R] + T_G_Y[G] + T_B_Y[B]) >> 14
    Cb = (T_R_CB[R] + T_G_CB[G] + T_B_CB[B]) >> 14
    Cr = (T_R_CR[R] + T_G_CR[G] + T_B_CR[B]) >> 14
    return Y, Cb, Cr


def subsample_420(C):
    """Sous-échantillonnage d'origine (@0x34d0) : somme 2x2 + dither (1,2,1,2.. selon la parité de colonne) puis >>2."""
    h, w = C.shape
    s = C[0:h:2, 0:w:2] + C[0:h:2, 1:w:2] + C[1:h:2, 0:w:2] + C[1:h:2, 1:w:2]
    d = 1 + (np.arange(w // 2) & 1)
    return (s + d[None, :]) >> 2


class _BitWriter:
    __slots__ = ('buf', 'acc', 'n')

    def __init__(self):
        self.buf = bytearray()
        self.acc = 0
        self.n = 0

    def put(self, code, length):
        self.acc = (self.acc << length) | (code & ((1 << length) - 1))
        self.n += length
        while self.n >= 8:
            self.n -= 8
            byte = (self.acc >> self.n) & 0xFF
            self.buf.append(byte)
            if byte == 0xFF:
                self.buf.append(0)
        self.acc &= (1 << self.n) - 1

    def flush(self):
        # d'origine (@0x35c0) : écrit 7 bits à 1 ; seuls les octets complets sont émis => bourrage à 1 jusqu'à la frontière d'octet
        self.put(0x7F, 7)


def _bitlen(v):
    return int(v).bit_length()


def _encode_block(bw, coefs, comp, last_dc):
    """coefs : liste de 64 ints (ordre naturel). comp : 0 = luma, 1/2 = chroma. Retourne le nouveau prédicteur DC."""
    t = 0 if comp == 0 else 1
    dch, ach = DC_HUFF[t], AC_HUFF[t]
    dc = int(coefs[0])
    diff = dc - last_dc
    mag = -diff if diff < 0 else diff
    size = _bitlen(mag)
    if size > 11:
        raise ValueError('DC trop grand (la DLL d\'origine quitte le processus)')
    code, ln = dch[size]
    bw.put(code, ln)
    if size:
        bw.put(diff if diff >= 0 else diff - 1, size)
    run = 0
    for k in ZIGZAG[1:]:
        v = int(coefs[k])
        if v == 0:
            run += 1
            continue
        while run > 15:
            code, ln = ach[0xF0]
            bw.put(code, ln)
            run -= 16
        mag = -v if v < 0 else v
        size = _bitlen(mag)
        if size > 10:
            raise ValueError('AC trop grand (la DLL d\'origine quitte le processus)')
        code, ln = ach[(run << 4) | size]
        bw.put(code, ln)
        bw.put(v if v >= 0 else v - 1, size)
        run = 0
    if run > 0:
        code, ln = ach[0x00]
        bw.put(code, ln)
    return dc


def quantized_blocks(bgr_mem, zero_triangle=True):
    """Étapes couleur -> DCT -> quantification. Retourne (qy[mr,mc,2,2,64], qcb[mr,mc,64], qcr[mr,mc,64], partial)."""
    h, w, _ = bgr_mem.shape
    if w % 16 or h % 8:
        raise ValueError('largeur multiple de 16 et hauteur multiple de 8 requises (limite de la DLL d\'origine)')
    mcu_cols = w // 16
    mcu_rows = (h + 15) // 16
    partial = (h % 16) == 8           # dernière rangée de MCU de 8 lignes seulement (cas 120 et 600 de la DLL)
    Y, Cb, Cr = rgb_to_ycc_planes(bgr_mem)
    Cbs = subsample_420(Cb)
    Crs = subsample_420(Cr)
    if partial:   # réplication de la dernière ligne valide (copie 0x3470)
        Y = np.concatenate([Y, np.repeat(Y[-1:], 8, axis=0)], axis=0)
        Cbs = np.concatenate([Cbs, np.repeat(Cbs[-1:], 4, axis=0)], axis=0)
        Crs = np.concatenate([Crs, np.repeat(Crs[-1:], 4, axis=0)], axis=0)
    Yb = (Y.reshape(mcu_rows, 2, 8, mcu_cols, 2, 8).transpose(0, 3, 1, 4, 2, 5) - 128)
    Cbb = (Cbs.reshape(mcu_rows, 8, mcu_cols, 8).transpose(0, 2, 1, 3) - 128)
    Crb = (Crs.reshape(mcu_rows, 8, mcu_cols, 8).transpose(0, 2, 1, 3) - 128)
    qy = quantize_blocks(fdct_blocks(Yb.reshape(-1, 8, 8)), True, zero_triangle).reshape(mcu_rows, mcu_cols, 2, 2, 64)
    qcb = quantize_blocks(fdct_blocks(Cbb.reshape(-1, 8, 8)), False, zero_triangle).reshape(mcu_rows, mcu_cols, 64)
    qcr = quantize_blocks(fdct_blocks(Crb.reshape(-1, 8, 8)), False, zero_triangle).reshape(mcu_rows, mcu_cols, 64)
    return qy, qcb, qcr, partial


def encode_scan_from_quantized(qy, qcb, qcr, partial=False):
    """Codage entropique (Huffman standard) de coefficients quantifiés -> FFD8 + données + FFD9."""
    mcu_rows, mcu_cols = qcb.shape[:2]
    bw = _BitWriter()
    last = [0, 0, 0]
    zero = [0] * 64
    for r in range(mcu_rows):
        last_row = partial and r == mcu_rows - 1
        for c in range(mcu_cols):
            for by in range(2):
                for bx in range(2):
                    if last_row and by == 1:
                        # bloc « manquant » : AC = 0, DC = DC du bloc précédent dans l'ordre de codage (@0x3000)
                        blk = zero[:]
                        blk[0] = last[0]
                        last[0] = _encode_block(bw, blk, 0, last[0])
                    else:
                        last[0] = _encode_block(bw, qy[r, c, by, bx].tolist(), 0, last[0])
            last[1] = _encode_block(bw, qcb[r, c].tolist(), 1, last[1])
            last[2] = _encode_block(bw, qcr[r, c].tolist(), 2, last[2])
    bw.flush()
    return b'\xff\xd8' + bytes(bw.buf) + b'\xff\xd9'


def encode_frame(bgr_mem):
    """Encode une image (h, w, 3) uint8 BGR en ordre mémoire DIB (première ligne = ligne du bas de l'image visible).
    Retourne les octets du chunk 00dc : FFD8 + données entropiques + FFD9, identiques à AMV_EncDLL.dll."""
    qy, qcb, qcr, partial = quantized_blocks(bgr_mem)
    return encode_scan_from_quantized(qy, qcb, qcr, partial)


# --------------------------------------------------------------------------------------------
# AUDIO : ancien audio_resample de libavcodec (copié dans AMV_EncDLL) + ADPCM IMA (bloc AMV)
# --------------------------------------------------------------------------------------------

IMA_STEP = [7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 19, 21, 23, 25, 28, 31, 34, 37, 41, 45, 50, 55, 60, 66, 73, 80, 88, 97, 107, 118, 130, 143, 157,
            173, 190, 209, 230, 253, 279, 307, 337, 371, 408, 449, 494, 544, 598, 658, 724, 796, 876, 963, 1060, 1166, 1282, 1411, 1552, 1707,
            1878, 2066, 2272, 2499, 2749, 3024, 3327, 3660, 4026, 4428, 4871, 5358, 5894, 6484, 7132, 7845, 8630, 9493, 10442, 11487, 12635,
            13899, 15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794, 32767]
IMA_INDEX = [-1, -1, -1, -1, 2, 4, 6, 8, -1, -1, -1, -1, 2, 4, 6, 8]


def _f32(x):
    return float(_struct.unpack('<f', _struct.pack('<f', x))[0])


class MonoResampler:
    """Réplique de init_mono_resample / mono_resample (libavcodec 2005, copiée dans AMV_EncDLL @0x1a30..0x1f30)."""
    FRAC_ONE = 1 << 16

    def __init__(self, ratio_f32):
        inv = _f32(1.0 / ratio_f32)
        self.iratio = int(_math.floor(1.0 / ratio_f32))
        if self.iratio == 0:
            self.iratio = 1
        self.incr = int((inv / self.iratio) * 65536.0)          # troncature (_ftol)
        self.frac = self.FRAC_ONE
        self.last_sample = 0
        self.icount = self.iratio
        self.isum = 0
        self.inv = self.FRAC_ONE // self.iratio

    def _integer_downsample(self, x):
        out = []
        c, s = self.icount, self.isum
        inv = self.inv
        for v in x:
            s += v
            c -= 1
            if c == 0:
                out.append((s * inv) >> 16)
                c = self.iratio
                s = 0
        self.isum, self.icount = s, c
        return out

    def _fractional(self, x):
        n = len(x)
        if n == 0:
            return []
        l0, frac, incr = self.last_sample, self.frac, self.incr
        out = []
        p = 0
        l1 = x[p]
        p += 1
        while True:
            v = ((l0 * (0x10000 - frac) + l1 * frac) & 0xFFFFFFFF) >> 16
            v &= 0xFFFF
            out.append(v - 65536 if v >= 32768 else v)
            frac += incr
            while frac >= 0x10000:
                frac -= 0x10000
                if p >= n:
                    self.last_sample, self.frac = l1, frac
                    return out
                l0 = l1
                l1 = x[p]
                p += 1

    def process(self, x):
        if self.iratio > 1:
            x = self._integer_downsample(x)
        if self.incr != self.FRAC_ONE:
            return self._fractional(x)
        return list(x)


class ImaAdpcmAmvEncoder:
    """Encodeur ADPCM de AMV_EncDLL @0x1fa0 (algorithme de référence Intel/DVI), état persistant entre blocs."""

    def __init__(self):
        self.pred = 0
        self.index = 0

    def encode(self, samples):
        pred, index = self.pred, self.index
        out = bytearray()
        step = IMA_STEP[index]
        hi = None
        for s in samples:
            diff = s - pred
            sign = 8 if diff < 0 else 0
            if sign:
                diff = -diff
            delta = 0
            vpdiff = step >> 3
            st = step
            if diff >= st:
                delta = 4
                diff -= st
                vpdiff += st
            st >>= 1
            if diff >= st:
                delta |= 2
                diff -= st
                vpdiff += st
            st >>= 1
            if diff >= st:
                delta |= 1
                vpdiff += st
            pred = pred - vpdiff if sign else pred + vpdiff
            if pred > 32767:
                pred = 32767
            elif pred < -32768:
                pred = -32768
            delta |= sign
            index += IMA_INDEX[delta]
            if index < 0:
                index = 0
            elif index > 88:
                index = 88
            step = IMA_STEP[index]
            if hi is None:
                hi = (delta & 0xF) << 4
            else:
                out.append((delta & 0xF) | hi)
                hi = None
        if hi is not None:
            out.append(hi)
        self.pred, self.index = pred, index
        return bytes(out)


class AmvAudioEncoder:
    """Chaîne audio d'AMV_EncDLL : PCM s16 (1 ou 2 canaux) -> mono -> rééchantillonnage -> blocs 01wb (8 octets d'en-tête + ADPCM)."""

    def __init__(self, src_rate, src_channels, out_rate_max):
        if src_channels not in (1, 2):
            raise ValueError('1 ou 2 canaux seulement (limite de la DLL d\'origine)')
        self.src_rate = src_rate
        self.src_channels = src_channels
        self.out_rate = min(src_rate, out_rate_max)                 # WAVEFORMATEX : min(source, 22050|32000)
        self.ratio = _f32(self.out_rate / src_rate)
        self.res = MonoResampler(self.ratio)
        self.adpcm = ImaAdpcmAmvEncoder()

    def block(self, pcm_interleaved):
        """pcm_interleaved : séquence d'int16 (n_in * src_channels). Retourne le payload du chunk 01wb."""
        if self.src_channels == 2:
            mono = [(pcm_interleaved[2 * i] + pcm_interleaved[2 * i + 1]) >> 1 for i in range(len(pcm_interleaved) // 2)]
        else:
            mono = list(pcm_interleaved)
        if self.src_channels == 1 and self.ratio == 1.0:
            res = mono
        else:
            res = self.res.process(mono)
        pred0, idx0 = self.adpcm.pred, self.adpcm.index         # l'en-tête reprend l'état AVANT encodage
        nib = self.adpcm.encode(res)
        return _struct.pack('<hBBI', pred0, idx0, 0, len(res)) + nib


# --------------------------------------------------------------------------------------------
# CONTENEUR AMV (AmvHeaderEncoder @0x17c0 + fin de conversion de transdll.dll @0x7270)
# --------------------------------------------------------------------------------------------
AMV_HEADER_SIZE = 0x13C


def amv_header(width, height, fps, out_rate, movi_payload_bytes, duration_seconds):
    """En-tête de 316 octets. movi_payload_bytes = somme des (8 + taille) de tous les chunks 00dc/01wb."""
    h = bytearray()
    h += b'RIFF' + _struct.pack('<I', 0) + b'AMV '
    h += b'LIST' + _struct.pack('<I', 0) + b'hdrl'
    h += b'amvh' + _struct.pack('<I', 0x38)
    sec = int(duration_seconds)
    dur = _struct.pack('<BBH', sec % 60, (sec // 60) % 60, sec // 3600)
    h += _struct.pack('<IIIIIIIIIIIII', 1000000 // fps, 0, 0, 1, 0, 0, 0, 0, width, height, fps, 1, 0) + dur
    h += b'LIST' + _struct.pack('<I', 0) + b'strl'
    h += b'strh' + _struct.pack('<I', 0x38) + bytes(0x38)
    h += b'strf' + _struct.pack('<I', 0x24) + bytes(0x24)
    h += b'LIST' + _struct.pack('<I', 0) + b'strl'
    h += b'strh' + _struct.pack('<I', 0x30) + bytes(0x30)
    h += b'strf' + _struct.pack('<I', 0x14) + _struct.pack('<HHIIHHHH', 1, 1, out_rate, out_rate * 2, 2, 16, 0, 0)
    h += b'LIST' + _struct.pack('<I', 12 + movi_payload_bytes) + b'movi'
    return bytes(h)


def amv_idx1(chunk_sizes):
    """chunk_sizes : liste de (tag, taille_payload) dans l'ordre du fichier. Offsets relatifs à 'movi' (premier chunk = 4)."""
    off = 4
    body = bytearray()
    for tag, size in chunk_sizes:
        body += tag + _struct.pack('<III', 0x10, off, size)
        off += 8 + size
    return b'idx1' + _struct.pack('<I', len(body)) + bytes(body)


def build_amv_file(width, height, fps, out_rate, video_chunks, audio_chunks, duration_seconds):
    """Assemble : en-tête | (00dc,01wb)* | 'AMV_END_' | idx1  (ordre et valeurs identiques à transdll.dll)."""
    movi = bytearray()
    sizes = []
    for v, a in zip(video_chunks, audio_chunks):
        movi += b'00dc' + _struct.pack('<I', len(v)) + v
        movi += b'01wb' + _struct.pack('<I', len(a)) + a
        sizes += [(b'00dc', len(v)), (b'01wb', len(a))]
    head = amv_header(width, height, fps, out_rate, len(movi), duration_seconds)
    return head + bytes(movi) + b'AMV_END_' + amv_idx1(sizes)


# --------------------------------------------------------------------------------------------
# DÉCODAGE entropique JPEG baseline (4:2:0, tables standard) : utilisé pour l'analyse, le lecteur et les vérifications
# --------------------------------------------------------------------------------------------
def _invert_huff(table):
    return {(ln, code): sym for sym, (code, ln) in table.items()}


_DC_INV = (_invert_huff(DC_HUFF[0]), _invert_huff(DC_HUFF[1]))
_AC_INV = (_invert_huff(AC_HUFF[0]), _invert_huff(AC_HUFF[1]))


def _unstuff(data):
    out = bytearray()
    i = 0
    n = len(data)
    while i < n:
        b = data[i]
        out.append(b)
        if b == 0xFF and i + 1 < n and data[i + 1] == 0x00:
            i += 1
        i += 1
    return bytes(out)


def decode_scan(scan, mcu_rows, mcu_cols):
    """scan : octets entropiques (après SOS, avant EOI). Retourne (qy[mr,mc,2,2,64], qcb[mr,mc,64], qcr[mr,mc,64]) en ordre naturel."""
    data = _unstuff(scan)
    bits = int.from_bytes(data, 'big') if data else 0
    nbits = len(data) * 8
    pos = [0]

    def getbit():
        p = pos[0]
        pos[0] = p + 1
        if p >= nbits:
            return 1
        return (bits >> (nbits - 1 - p)) & 1

    def getbits(n):
        v = 0
        for _ in range(n):
            v = (v << 1) | getbit()
        return v

    def huff(inv):
        code = 0
        for ln in range(1, 17):
            code = (code << 1) | getbit()
            s = inv.get((ln, code))
            if s is not None:
                return s
        raise ValueError('code Huffman invalide')

    def ext(v, n):
        return v if v >= (1 << (n - 1)) else v - (1 << n) + 1

    def block(comp, last):
        t = 0 if comp == 0 else 1
        blk = [0] * 64
        s = huff(_DC_INV[t])
        diff = ext(getbits(s), s) if s else 0
        dc = last + diff
        blk[0] = dc
        k = 1
        while k < 64:
            rs = huff(_AC_INV[t])
            r, s = rs >> 4, rs & 15
            if s == 0:
                if r == 15:
                    k += 16
                    continue
                break
            k += r
            if k > 63:
                break
            blk[ZIGZAG[k]] = ext(getbits(s), s)
            k += 1
        return blk, dc

    qy = np.zeros((mcu_rows, mcu_cols, 2, 2, 64), np.int64)
    qcb = np.zeros((mcu_rows, mcu_cols, 64), np.int64)
    qcr = np.zeros((mcu_rows, mcu_cols, 64), np.int64)
    last = [0, 0, 0]
    for r in range(mcu_rows):
        for c in range(mcu_cols):
            for by in range(2):
                for bx in range(2):
                    b, last[0] = block(0, last[0])
                    qy[r, c, by, bx] = b
            b, last[1] = block(1, last[1])
            qcb[r, c] = b
            b, last[2] = block(2, last[2])
            qcr[r, c] = b
    return qy, qcb, qcr


# --------------------------------------------------------------------------------------------
# SORTIE AVI (AVI_EncDLL.dll) : MJPEG complet + IMA ADPCM « WAV » à blocs fixes — reconstruction
# --------------------------------------------------------------------------------------------
AVI_OUT_RATE = 22050


def _dqt(tid, table_nat):
    zz = bytes(int(table_nat[k]) for k in ZIGZAG)
    return b'\xff\xdb' + _struct.pack('>H', 67) + bytes([tid]) + zz


def _dht(tc_th, bits, vals):
    return b'\xff\xc4' + _struct.pack('>H', 2 + 1 + 16 + len(vals)) + bytes([tc_th]) + bytes(bits) + bytes(vals)


def avi_jpeg_header(width, height):
    h = b'\xff\xd8'
    h += b'\xff\xe0' + _struct.pack('>H', 16) + b'AVI1' + bytes(10)
    h += _dqt(0, QY) + _dqt(1, QC)
    h += b'\xff\xc0' + _struct.pack('>H', 17) + bytes([8]) + _struct.pack('>HH', height, width) + bytes([3, 1, 0x22, 0, 2, 0x11, 1, 3, 0x11, 1])
    h += _dht(0x00, _DC_L_BITS, _DC_L_VALS) + _dht(0x10, _AC_L_BITS, _AC_L_VALS)
    h += _dht(0x01, _DC_C_BITS, _DC_C_VALS) + _dht(0x11, _AC_C_BITS, _AC_C_VALS)
    h += b'\xff\xda' + _struct.pack('>H', 12) + bytes([3, 1, 0x00, 2, 0x11, 3, 0x11, 0, 63, 0])
    return h


def encode_frame_avi(bgr_mem, zero_triangle=False):
    """Une image AVI : l'entrée est au format DIB (lignes du bas d'abord) ; la DLL la retourne verticalement avant le JPEG."""
    h, w, _ = bgr_mem.shape
    flipped = np.ascontiguousarray(bgr_mem[::-1])
    qy, qcb, qcr, partial = quantized_blocks(flipped, zero_triangle=zero_triangle)
    mcu_rows, mcu_cols = qcb.shape[:2]
    bw = _BitWriter()
    last = [0, 0, 0]
    zero = [0] * 64
    for r in range(mcu_rows):
        last_row = partial and r == mcu_rows - 1
        for c in range(mcu_cols):
            for by in range(2):
                for bx in range(2):
                    if last_row and by == 1:
                        blk = zero[:]
                        blk[0] = last[0]
                        last[0] = _encode_block(bw, blk, 0, last[0])
                    else:
                        last[0] = _encode_block(bw, qy[r, c, by, bx].tolist(), 0, last[0])
            last[1] = _encode_block(bw, qcb[r, c].tolist(), 1, last[1])
            last[2] = _encode_block(bw, qcr[r, c].tolist(), 2, last[2])
    bw.flush()
    return avi_jpeg_header(w, h) + bytes(bw.buf) + b'\xff\xd9'


def avi_samples_per_block(fps):
    """AviEncoderInit : fps >= 18 -> 1017 échantillons par bloc audio, sinon 1529."""
    return 1017 if fps >= 18 else 1529


class ImaAdpcmWavEncoder:
    """Bloc ADPCM IMA de AVI_EncDLL @0x2290/0x23f0 : en-tête 4 o (1er échantillon int16 + index u16), puis count-1 nibbles ; l'index persiste."""

    def __init__(self, low_nibble_first=False):
        self.index = 0
        self.low_first = low_nibble_first

    def block(self, samples):
        pred = int(samples[0])
        index = self.index
        out = bytearray(_struct.pack('<hH', pred, index))
        step = IMA_STEP[index]
        pending = None
        for s in samples[1:]:
            diff = s - pred
            sign = 8 if diff < 0 else 0
            if sign:
                diff = -diff
            delta = 0
            vpdiff = step >> 3
            st = step
            if diff >= st:
                delta = 4
                diff -= st
                vpdiff += st
            st >>= 1
            if diff >= st:
                delta |= 2
                diff -= st
                vpdiff += st
            st >>= 1
            if diff >= st:
                delta |= 1
                vpdiff += st
            pred = pred - vpdiff if sign else pred + vpdiff
            pred = 32767 if pred > 32767 else (-32768 if pred < -32768 else pred)
            delta |= sign
            index += IMA_INDEX[delta]
            index = 0 if index < 0 else (88 if index > 88 else index)
            step = IMA_STEP[index]
            if pending is None:
                pending = delta & 0xF
            else:
                out.append((pending | ((delta & 0xF) << 4)) if self.low_first else (((pending << 4) | (delta & 0xF)) & 0xFF))
                pending = None
        if pending is not None:
            out.append(pending if self.low_first else ((pending << 4) & 0xFF))
        self.index = index
        return bytes(out)


def avi_header(width, height, nframes, spb, movi_data_bytes, idx1_bytes, duration_seconds=0, out_rate=AVI_OUT_RATE):
    blockalign = 4 + (spb - 1) // 2
    usec = int(1e6 * spb / out_rate)
    avg = int(out_rate * blockalign / spb)
    h = bytearray()
    h += b'RIFF' + _struct.pack('<I', 320 + movi_data_bytes + idx1_bytes) + b'AVI '
    h += b'LIST' + _struct.pack('<I', 296) + b'hdrl'
    h += b'avih' + _struct.pack('<I', 56)
    h += _struct.pack('<14I', usec, 262144, 0, 0x10010, nframes, 0, 2, 262144, width, height, (1024 * 1000000) // usec, 1, 0, int(duration_seconds))
    h += b'LIST' + _struct.pack('<I', 116) + b'strl'
    h += b'strh' + _struct.pack('<I', 56) + b'vids' + b'MJPG' + _struct.pack('<IHHIIIIIIIII', 0, 0, 0, 0, usec, 1000000, 0, 2, 0, 0, 0, 0)
    h += _struct.pack('<I', width | (height << 16))
    h += b'strf' + _struct.pack('<I', 40) + _struct.pack('<IiiHH', 40, width, height, 1, 24) + b'MJPG' + _struct.pack('<IIIII', width * height * 3, 0, 0, 0, 0)
    h += b'LIST' + _struct.pack('<I', 96) + b'strl'
    h += b'strh' + _struct.pack('<I', 56) + b'auds' + _struct.pack('<I', 0) + _struct.pack('<IHHIIIIIIIII', 0, 0, 0, 0, blockalign, avg, 0, (blockalign // 2 + 2) * nframes, blockalign // 2 + 2, 0, blockalign, 0)
    h += _struct.pack('<I', 0)
    h += b'strf' + _struct.pack('<I', 20) + _struct.pack('<HHIIHHHH', 0x11, 1, out_rate, avg, blockalign, 4, 2, spb)
    h += b'LIST' + _struct.pack('<I', 4 + movi_data_bytes) + b'movi'
    return bytes(h)


# --------------------------------------------------------------------------------------------
# DÉCODEUR vidéo (AMV_DecDLL.dll = IJG 6b : jidctint « islow », tables 8,6,5…) — reconstruction
# --------------------------------------------------------------------------------------------
_F = dict(f0298=2446, f0390=3196, f0541=4433, f0765=6270, f0899=7373, f1175=9633, f1501=12299, f1847=15137, f1961=16069, f2053=16819, f2562=20995, f3072=25172)


def _idct_1d(v, descale_bits, shift_dc=True):
    """v : liste de 8 tableaux int64 (entrées dé-quantifiées). Retourne 8 tableaux (sorties avant range-limit), IJG jidctint."""
    in0, in1, in2, in3, in4, in5, in6, in7 = v
    z2, z3 = in2, in6
    z1 = (z2 + z3) * _F['f0541']
    tmp2 = z1 + z3 * (-_F['f1847'])
    tmp3 = z1 + z2 * _F['f0765']
    tmp0 = (in0 + in4) << 13
    tmp1 = (in0 - in4) << 13
    tmp10, tmp13, tmp11, tmp12 = tmp0 + tmp3, tmp0 - tmp3, tmp1 + tmp2, tmp1 - tmp2
    t0, t1, t2, t3 = in7, in5, in3, in1
    z1 = t0 + t3
    z2 = t1 + t2
    z3 = t0 + t2
    z4 = t1 + t3
    z5 = (z3 + z4) * _F['f1175']
    t0 = t0 * _F['f0298']
    t1 = t1 * _F['f2053']
    t2 = t2 * _F['f3072']
    t3 = t3 * _F['f1501']
    z1 = z1 * (-_F['f0899'])
    z2 = z2 * (-_F['f2562'])
    z3 = z3 * (-_F['f1961']) + z5
    z4 = z4 * (-_F['f0390']) + z5
    t0 = t0 + z1 + z3
    t1 = t1 + z2 + z4
    t2 = t2 + z2 + z3
    t3 = t3 + z1 + z4
    rnd = 1 << (descale_bits - 1)
    out = [(tmp10 + t3 + rnd) >> descale_bits, (tmp11 + t2 + rnd) >> descale_bits, (tmp12 + t1 + rnd) >> descale_bits, (tmp13 + t0 + rnd) >> descale_bits,
           (tmp13 - t0 + rnd) >> descale_bits, (tmp12 - t1 + rnd) >> descale_bits, (tmp11 - t2 + rnd) >> descale_bits, (tmp10 - t3 + rnd) >> descale_bits]
    return out


def idct_islow_blocks(coefs, quant):
    """coefs : (N,64) ordre naturel ; quant : (64,). Retourne (N,8,8) échantillons 0..255 (range-limit IJG)."""
    c = (coefs.astype(np.int64) * quant[None, :].astype(np.int64)).reshape(-1, 8, 8)
    # passe 1 : colonnes (entrées c[:, k, col]) ; sortie ws[:, k, col] avec PASS1_BITS=2
    cols = _idct_1d([c[:, k, :] for k in range(8)], 11)
    ws = np.stack(cols, axis=1)
    # passe 2 : lignes
    rows = _idct_1d([ws[:, :, k] for k in range(8)], 18)
    out = np.stack(rows, axis=2)
    v = out & 1023
    return np.where(v < 128, v + 128, np.where(v < 512, 255, np.where(v < 896, 0, v - 896)))


def _fancy_h2v2(plane):
    """Suréchantillonnage IJG h2v2_fancy_upsample (triangle 3/4,1/4) ; plane (h,w) -> (2h,2w), bords répliqués comme IJG."""
    h, w = plane.shape
    p = plane.astype(np.int64)
    up = np.empty((2 * h, w), np.int64)
    above = np.vstack([p[:1], p[:-1]])
    below = np.vstack([p[1:], p[-1:]])
    up[0::2] = 3 * p + above
    up[1::2] = 3 * p + below
    out = np.empty((2 * h, 2 * w), np.int64)
    left = np.hstack([up[:, :1], up[:, :-1]])
    right = np.hstack([up[:, 1:], up[:, -1:]])
    out[:, 0::2] = (3 * up + left + 8) >> 4
    out[:, 1::2] = (3 * up + right + 7) >> 4
    out[:, 0] = (up[:, 0] * 4 + 8) >> 4
    out[:, -1] = (up[:, -1] * 4 + 7) >> 4
    return out


def _replicate_h2v2(plane):
    return np.repeat(np.repeat(plane.astype(np.int64), 2, axis=0), 2, axis=1)


def _ycc_to_bgr(Y, Cb, Cr):
    x = np.arange(256, dtype=np.int64) - 128
    one_half = 1 << 15
    cr_r = (91881 * x + one_half) >> 16          # FIX(1.40200)
    cb_b = (116130 * x + one_half) >> 16         # FIX(1.77200)
    cr_g = -46802 * x                            # FIX(0.71414)
    cb_g = -22554 * x + one_half                 # FIX(0.34414)
    def clamp(a):
        return np.clip(a, 0, 255)
    R = clamp(Y + cr_r[Cr])
    G = clamp(Y + ((cb_g[Cb] + cr_g[Cr]) >> 16))
    B = clamp(Y + cb_b[Cb])
    return np.stack([B, G, R], axis=-1).astype(np.uint8)


def decode_frame_bgr_reference(chunk, width, height, fancy=None):
    """Décode un chunk 00dc (FFD8 ... FFD9) en image BGR (h,w,3) dans l'ordre mémoire DIB (lignes dans l'ordre du flux)."""
    scan = chunk[2:-2] if chunk[-2:] == b'\xff\xd9' else chunk[2:]
    mcu_cols = width // 16
    mcu_rows = (height + 15) // 16
    qy, qcb, qcr = decode_scan(scan, mcu_rows, mcu_cols)
    Yb = idct_islow_blocks(qy.reshape(-1, 64), QY).reshape(mcu_rows, mcu_cols, 2, 2, 8, 8)
    Y = Yb.transpose(0, 2, 4, 1, 3, 5).reshape(mcu_rows * 16, mcu_cols * 16)
    Cb = idct_islow_blocks(qcb.reshape(-1, 64), QC).reshape(mcu_rows, mcu_cols, 8, 8).transpose(0, 2, 1, 3).reshape(mcu_rows * 8, mcu_cols * 8)
    Cr = idct_islow_blocks(qcr.reshape(-1, 64), QC).reshape(mcu_rows, mcu_cols, 8, 8).transpose(0, 2, 1, 3).reshape(mcu_rows * 8, mcu_cols * 8)
    up = _vendor_upsample_h2v2 if fancy is None else (_fancy_h2v2 if fancy else _replicate_h2v2)
    img = _ycc_to_bgr(Y.astype(np.int64), up(Cb), up(Cr))
    return img[:height, :width]


def _vendor_upsample_h2v2(plane):
    """Suréchantillonnage chroma de AMV_DecDLL @0x2c40 : par MCU (8 -> 16 échantillons/ligne) :
    sortie[2k+1] = s[k] ; sortie[2k] = (s[k]+s[k+1])>>1 (k<7) ; sortie[14] = (s6+s7)>>1 ; sortie[15] = s7.  Verticalement : réplication."""
    h, w = plane.shape
    p = plane.astype(np.int64).reshape(h, w // 8, 8)
    out = np.empty((h, w // 8, 16), np.int64)
    out[..., 1::2] = p
    out[..., 0:14:2] = (p[..., 0:7] + p[..., 1:8]) >> 1
    out[..., 14] = (p[..., 6] + p[..., 7]) >> 1
    out = out.reshape(h, w * 2)
    return np.repeat(out, 2, axis=0)


class ImaAdpcmAmvDecoder:
    """Décodage d'un bloc 01wb : en-tête 8 o (prédicteur int16, index u8, 0, n u32) puis nibbles (poids fort d'abord)."""

    @staticmethod
    def block(payload):
        pred, index, _pad, n = _struct.unpack('<hBBI', payload[:8])
        out = []
        data = payload[8:]
        step = IMA_STEP[index]
        for i in range(n):
            b = data[i >> 1]
            nib = (b >> 4) if (i & 1) == 0 else (b & 0xF)
            diff = step >> 3
            if nib & 4:
                diff += step
            if nib & 2:
                diff += step >> 1
            if nib & 1:
                diff += step >> 2
            pred = pred - diff if nib & 8 else pred + diff
            pred = 32767 if pred > 32767 else (-32768 if pred < -32768 else pred)
            index += IMA_INDEX[nib]
            index = 0 if index < 0 else (88 if index > 88 else index)
            step = IMA_STEP[index]
            out.append(pred)
        return out


# --------------------------------------------------------------------------------------------
# Décodage entropique RAPIDE (table de recherche sur 16 bits) — équivalent à decode_scan
# --------------------------------------------------------------------------------------------
def _build_lut(table):
    lut = [0] * 65536
    for sym, (code, ln) in table.items():
        base = code << (16 - ln)
        v = (ln << 8) | sym
        for k in range(1 << (16 - ln)):
            lut[base + k] = v
    return lut


_DC_LUT = (_build_lut(DC_HUFF[0]), _build_lut(DC_HUFF[1]))
_AC_LUT = (_build_lut(AC_HUFF[0]), _build_lut(AC_HUFF[1]))


def decode_scan_fast(scan, mcu_rows, mcu_cols):
    data = _unstuff(scan)
    n = len(data)
    pos = 0
    acc = 0
    nb = 0
    zz = ZIGZAG
    out_y = np.zeros((mcu_rows, mcu_cols, 2, 2, 64), np.int64)
    out_cb = np.zeros((mcu_rows, mcu_cols, 64), np.int64)
    out_cr = np.zeros((mcu_rows, mcu_cols, 64), np.int64)
    last = [0, 0, 0]
    for r in range(mcu_rows):
        for c in range(mcu_cols):
            for bi in range(6):
                t = 0 if bi < 4 else 1
                ci = 0 if bi < 4 else bi - 3
                dcl = _DC_LUT[t]
                acl = _AC_LUT[t]
                blk = [0] * 64
                # --- DC
                while nb < 16:
                    acc = ((acc << 8) | (data[pos] if pos < n else 0xFF)) & 0xFFFFFFFFFFFF
                    pos += 1
                    nb += 8
                v = dcl[(acc >> (nb - 16)) & 0xFFFF]
                nb -= v >> 8
                s = v & 255
                if s:
                    while nb < s:
                        acc = ((acc << 8) | (data[pos] if pos < n else 0xFF)) & 0xFFFFFFFFFFFF
                        pos += 1
                        nb += 8
                    bits = (acc >> (nb - s)) & ((1 << s) - 1)
                    nb -= s
                    diff = bits if bits >= (1 << (s - 1)) else bits - (1 << s) + 1
                else:
                    diff = 0
                last[ci] += diff
                blk[0] = last[ci]
                k = 1
                while k < 64:
                    while nb < 16:
                        acc = ((acc << 8) | (data[pos] if pos < n else 0xFF)) & 0xFFFFFFFFFFFF
                        pos += 1
                        nb += 8
                    v = acl[(acc >> (nb - 16)) & 0xFFFF]
                    nb -= v >> 8
                    rs = v & 255
                    s = rs & 15
                    if s == 0:
                        if rs == 0xF0:
                            k += 16
                            continue
                        break
                    k += rs >> 4
                    if k > 63:
                        break
                    while nb < s:
                        acc = ((acc << 8) | (data[pos] if pos < n else 0xFF)) & 0xFFFFFFFFFFFF
                        pos += 1
                        nb += 8
                    bits = (acc >> (nb - s)) & ((1 << s) - 1)
                    nb -= s
                    blk[zz[k]] = bits if bits >= (1 << (s - 1)) else bits - (1 << s) + 1
                    k += 1
                if bi < 4:
                    out_y[r, c, bi >> 1, bi & 1] = blk
                elif bi == 4:
                    out_cb[r, c] = blk
                else:
                    out_cr[r, c] = blk
    return out_y, out_cb, out_cr



# --------------------------------------------------------------------------------------------
# Compléments : décodage rapide des images AMV/AVI, ADPCM WAV, chaîne audio mono
# --------------------------------------------------------------------------------------------
def _planes_to_bgr(qy, qcb, qcr, width, height, upsample=None):
    mr, mc = qcb.shape[:2]
    Yb = idct_islow_blocks(qy.reshape(-1, 64), QY).reshape(mr, mc, 2, 2, 8, 8)
    Y = Yb.transpose(0, 2, 4, 1, 3, 5).reshape(mr * 16, mc * 16)
    Cb = idct_islow_blocks(qcb.reshape(-1, 64), QC).reshape(mr, mc, 8, 8).transpose(0, 2, 1, 3).reshape(mr * 8, mc * 8)
    Cr = idct_islow_blocks(qcr.reshape(-1, 64), QC).reshape(mr, mc, 8, 8).transpose(0, 2, 1, 3).reshape(mr * 8, mc * 8)
    up = upsample or _vendor_upsample_h2v2
    img = _ycc_to_bgr(Y.astype(np.int64), up(Cb), up(Cr))
    return img[:height, :width]


def decode_frame_bgr(chunk, width, height, fancy=None):          # redéfinition : version rapide (identique, voir selftest)
    """Chunk AMV 00dc (FFD8 + données + FFD9) -> image BGR (h, w, 3) dans l'ORDRE DU FLUX (= ordre DIB : lignes du bas d'abord)."""
    scan = chunk[2:-2] if chunk[-2:] == b'\xff\xd9' else chunk[2:]
    qy, qcb, qcr = decode_scan_fast(scan, (height + 15) // 16, width // 16)
    return _planes_to_bgr(qy, qcb, qcr, width, height)


def avi_scan_from_chunk(chunk):
    """Extrait les données entropiques d'une image AVI (JPEG complet) : après le marqueur SOS, avant EOI."""
    i = 2
    n = len(chunk)
    while i + 4 <= n and chunk[i] == 0xFF:
        marker = chunk[i + 1]
        length = (chunk[i + 2] << 8) | chunk[i + 3]
        if marker == 0xDA:
            start = i + 2 + length
            end = n - 2 if chunk[n - 2:] == b'\xff\xd9' else n
            return chunk[start:end]
        i += 2 + length
    raise ValueError("JPEG sans marqueur SOS")


def decode_avi_frame_bgr(chunk, width, height):
    """Image AVI (JPEG complet) -> BGR (h, w, 3) À L'ENDROIT (ordre visible, première ligne = haut)."""
    qy, qcb, qcr = decode_scan_fast(avi_scan_from_chunk(chunk), (height + 15) // 16, width // 16)
    return _planes_to_bgr(qy, qcb, qcr, width, height, _replicate_h2v2)   # JPEG standard : réplication (51 dB vs ffmpeg)


class ImaAdpcmWavDecoder:
    """Décode un bloc 01wb de l'AVI : en-tête 4 o (échantillon int16, index u16) puis quartets, quartet BAS d'abord."""

    @staticmethod
    def block(payload, samples_per_block):
        pred, index = _struct.unpack('<hH', payload[:4])
        index = min(index, 88)
        out = [pred]
        data = payload[4:]
        step = IMA_STEP[index]
        for i in range(samples_per_block - 1):
            b = data[i >> 1] if (i >> 1) < len(data) else 0
            nib = (b & 0xF) if (i & 1) == 0 else (b >> 4)
            diff = step >> 3
            if nib & 4:
                diff += step
            if nib & 2:
                diff += step >> 1
            if nib & 1:
                diff += step >> 2
            pred = pred - diff if nib & 8 else pred + diff
            pred = 32767 if pred > 32767 else (-32768 if pred < -32768 else pred)
            index += IMA_INDEX[nib]
            index = 0 if index < 0 else (88 if index > 88 else index)
            step = IMA_STEP[index]
            out.append(pred)
        return out


class AudioMonoResampler:
    """Chaîne audio d'AMV_EncDLL / audio_resample sans ADPCM : PCM s16 (1 ou 2 canaux) -> mono -> fréquence de sortie.
    Même arithmétique que AmvAudioEncoder.block (vérifié par selftest)."""

    def __init__(self, src_rate, src_channels, out_rate):
        if src_channels not in (1, 2):
            raise ValueError('1 ou 2 canaux seulement')
        self.src_channels = src_channels
        self.out_rate = out_rate
        self.ratio = _f32(out_rate / src_rate)
        self.res = MonoResampler(self.ratio)

    def feed(self, pcm):
        if self.src_channels == 2:
            mono = [(pcm[2 * i] + pcm[2 * i + 1]) >> 1 for i in range(len(pcm) // 2)]
        else:
            mono = list(pcm)
        if self.src_channels == 1 and self.ratio == 1.0:
            return mono
        return self.res.process(mono) if mono else []



# ============================================================================================
# SOURCES MULTIMÉDIA : ffmpeg / ffprobe (remplacent DirectShow et FFMpegDll.dll du programme d'origine)
# ============================================================================================
FFMPEG_DIR_OVERRIDE = None


def find_tool(name):
    """Cherche ffmpeg/ffprobe : dossier choisi par l'utilisateur, variable MPU_FFMPEG_DIR, dossier du script, PATH."""
    exe = name + (".exe" if os.name == "nt" else "")
    here = os.path.dirname(os.path.abspath(__file__)) if "__file__" in globals() else os.getcwd()
    for d in (FFMPEG_DIR_OVERRIDE, os.environ.get("MPU_FFMPEG_DIR"), here, os.path.join(here, "ffmpeg", "bin"), os.path.join(here, "ffmpeg")):
        if d and os.path.isfile(os.path.join(d, exe)):
            return os.path.join(d, exe)
    return shutil.which(name)


class ToolError(RuntimeError):
    pass


def require_tool(name):
    p = find_tool(name)
    if not p:
        raise ToolError("%s introuvable : installez ffmpeg (https://ffmpeg.org) et placez-le dans le PATH, "
                        "à côté de mpu_toolkit.py, ou définissez MPU_FFMPEG_DIR." % name)
    return p


_NO_WINDOW = {"creationflags": 0x08000000} if os.name == "nt" else {}


class MediaInfo:
    def __init__(self):
        self.path = ""
        self.duration = 0.0
        self.has_video = False
        self.has_audio = False
        self.width = 0
        self.height = 0
        self.fps = 0.0
        self.vcodec = ""
        self.acodec = ""
        self.arate = 0
        self.achannels = 0
        self.container = ""

    def describe(self):
        v = "%dx%d %s %.2f i/s" % (self.width, self.height, self.vcodec, self.fps) if self.has_video else "(pas de vidéo)"
        a = "%s %d Hz %d canal(aux)" % (self.acodec, self.arate, self.achannels) if self.has_audio else "(pas d'audio)"
        return "%s | %s | %.2f s | %s" % (v, a, self.duration, self.container)


def _fraction(s):
    try:
        if "/" in str(s):
            a, b = str(s).split("/")
            return float(a) / float(b) if float(b) else 0.0
        return float(s)
    except Exception:
        return 0.0


def probe(path):
    """ffprobe -> MediaInfo."""
    ffprobe = require_tool("ffprobe")
    cp = subprocess.run([ffprobe, "-v", "error", "-print_format", "json", "-show_format", "-show_streams", path],
                        capture_output=True, text=True, **_NO_WINDOW)
    if cp.returncode != 0:
        raise ToolError("ffprobe n'a pas pu lire %s : %s" % (path, cp.stderr.strip()[:200]))
    d = json.loads(cp.stdout or "{}")
    mi = MediaInfo()
    mi.path = path
    fmt = d.get("format", {})
    mi.container = fmt.get("format_name", "")
    try:
        mi.duration = float(fmt.get("duration", 0) or 0)
    except ValueError:
        mi.duration = 0.0
    for s in d.get("streams", []):
        if s.get("codec_type") == "video" and not mi.has_video and s.get("disposition", {}).get("attached_pic", 0) == 0:
            mi.has_video = True
            mi.width = int(s.get("width", 0))
            mi.height = int(s.get("height", 0))
            mi.fps = _fraction(s.get("avg_frame_rate")) or _fraction(s.get("r_frame_rate"))
            mi.vcodec = s.get("codec_name", "")
            if not mi.duration:
                mi.duration = float(s.get("duration", 0) or 0)
        elif s.get("codec_type") == "audio" and not mi.has_audio:
            mi.has_audio = True
            mi.acodec = s.get("codec_name", "")
            mi.arate = int(s.get("sample_rate", 0) or 0)
            mi.achannels = int(s.get("channels", 0) or 0)
            if not mi.duration:
                mi.duration = float(s.get("duration", 0) or 0)
    return mi


def build_video_filter(orientation, aspect, width, height, fps_expr):
    """Chaîne de filtres ffmpeg : orientation, cadence, mise à l'échelle bicubique (étirement = comportement mesuré de FFMpegDll),
    puis retournement vertical final : les encodeurs d'origine reçoivent des images au format DIB (lignes du bas d'abord)."""
    f = []
    o = FFMPEG_ORIENT_FILTER.get(orientation, "")
    if o:
        f.append(o)
    f.append("fps=%s" % fps_expr)
    if aspect == "letterbox":
        f.append("scale=%d:%d:force_original_aspect_ratio=decrease:flags=bicubic,pad=%d:%d:(ow-iw)/2:(oh-ih)/2:color=black" % (width, height, width, height))
    elif aspect == "crop":
        f.append("scale=%d:%d:force_original_aspect_ratio=increase:flags=bicubic,crop=%d:%d" % (width, height, width, height))
    else:
        f.append("scale=%d:%d:flags=bicubic" % (width, height))
    f.append("setsar=1")
    f.append("vflip")
    return ",".join(f)


class FFVideoReader:
    """Lit des images BGR24 (w*h*3 octets) depuis ffmpeg."""

    def __init__(self, src, vf, width, height, start=0.0, duration=None):
        self.w, self.h = width, height
        self.size = width * height * 3
        cmd = [require_tool("ffmpeg"), "-hide_banner", "-loglevel", "error", "-nostdin"]
        if start:
            cmd += ["-ss", "%.3f" % start]
        cmd += ["-i", src, "-an", "-sn", "-vf", vf, "-f", "rawvideo", "-pix_fmt", "bgr24"]
        if duration:
            cmd += ["-t", "%.3f" % duration]
        cmd += ["-"]
        self.p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, **_NO_WINDOW)

    def read(self):
        buf = self.p.stdout.read(self.size)
        if len(buf) < self.size:
            return None
        return np.frombuffer(buf, np.uint8).reshape(self.h, self.w, 3)

    def close(self):
        try:
            self.p.stdout.close()
        except Exception:
            pass
        try:
            self.p.kill()
        except Exception:
            pass
        try:
            self.p.wait(timeout=5)
        except Exception:
            pass


class FFAudioReader:
    """Lit du PCM s16 entrelacé (fréquence et canaux imposés) depuis ffmpeg ; renvoie des tableaux int16."""

    def __init__(self, src, rate, channels, start=0.0, duration=None):
        self.ch = channels
        cmd = [require_tool("ffmpeg"), "-hide_banner", "-loglevel", "error", "-nostdin"]
        if start:
            cmd += ["-ss", "%.3f" % start]
        cmd += ["-i", src, "-map", "0:a:0", "-vn", "-sn", "-f", "s16le", "-acodec", "pcm_s16le", "-ac", str(channels), "-ar", str(rate)]
        if duration:
            cmd += ["-t", "%.3f" % duration]
        cmd += ["-"]
        self.p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, **_NO_WINDOW)
        self.eof = False

    def read(self, nframes):
        """Lit nframes échantillons par canal ; peut en renvoyer moins en fin de flux."""
        want = nframes * self.ch * 2
        buf = self.p.stdout.read(want)
        if len(buf) < want:
            self.eof = True
        buf = buf[: len(buf) - (len(buf) % (2 * self.ch))]
        return np.frombuffer(buf, "<i2")

    def close(self):
        try:
            self.p.stdout.close()
        except Exception:
            pass
        try:
            self.p.kill()
        except Exception:
            pass
        try:
            self.p.wait(timeout=5)
        except Exception:
            pass


class SilentAudio:
    """Source audio muette (fichier sans piste audio)."""

    def __init__(self, channels=1):
        self.ch = channels
        self.eof = False

    def read(self, nframes):
        return np.zeros(nframes * self.ch, "<i2")

    def close(self):
        pass


def apply_gain(pcm, gain):
    """Coefficient de volume ACOE de transdll (@0x6e50) : multiplication puis saturation 16 bits."""
    if gain == 1.0 or pcm.size == 0:
        return pcm
    return np.clip(np.rint(pcm.astype(np.float64) * gain), -32768, 32767).astype("<i2")


def to_rgb565(bgr):
    """Émulation de l'option « 16bit Bitmap color space » : quantification R5 G6 B5 puis réexpansion."""
    b = bgr[..., 0] >> 3
    g = bgr[..., 1] >> 2
    r = bgr[..., 2] >> 3
    out = np.empty_like(bgr)
    out[..., 0] = (b << 3) | (b >> 2)
    out[..., 1] = (g << 2) | (g >> 4)
    out[..., 2] = (r << 3) | (r >> 2)
    return out



# ============================================================================================
# MOTEUR DE CONVERSION (équivalent de CAmvTransform / CAviTransform de transdll.dll)
# ============================================================================================
from dataclasses import dataclass


class Cancelled(Exception):
    pass


@dataclass
class ConvertOptions:
    fmt: str = "amv"                 # "amv" ou "avi"
    width: int = 160
    height: int = 120
    fps: int = 30                    # AMV : cadence exacte ; AVI : sert à choisir 1017 (>=18) ou 1529 (<18) échantillons par bloc
    audio_rate: int = 22050          # AMV : 22050 ou 32000 (plafond ; jamais de sur-échantillonnage) ; AVI : toujours 22050
    orientation: str = "normal"
    aspect: str = "stretch"          # stretch | letterbox | crop
    start: float = 0.0               # découpe (secondes)
    end: float = 0.0                 # 0 = jusqu'à la fin
    audio_file: str = ""             # remplacement de la piste audio
    gain: float = 1.0                # ACOE
    rgb565: bool = False             # « 16bit Bitmap color space »
    insertwave: bool = True          # compléter l'audio manquant par du silence (sinon : s'arrêter avec l'audio)
    insertpic: bool = True           # compléter la vidéo manquante par des images noires (sinon : s'arrêter avec la vidéo)
    overwrite: bool = True
    outdir: str = ""
    vendor_updown_quirk: bool = False  # reproduit le défaut mesuré : « UpDown » = rotation de 180° dans le chemin FFmpeg d'origine


def validate_options(o):
    if o.fmt not in ("amv", "avi"):
        raise ValueError("format inconnu : %s" % o.fmt)
    if o.width % 16 or o.height % 8 or o.width < 16 or o.height < 8:
        raise ValueError("largeur multiple de 16 et hauteur multiple de 8 requises (limite des encodeurs d'origine)")
    if o.width > 1280:
        raise ValueError("largeur maximale 1280 (tampon de l'encodeur d'origine)")
    if not (1 <= int(o.fps) <= 60):
        raise ValueError("cadence entre 1 et 60 images/s")
    if o.fmt == "amv" and o.audio_rate not in AUDIO_RATES_AMV:
        raise ValueError("fréquence audio AMV : 22050 ou 32000 Hz")
    if o.orientation not in ORIENTATIONS:
        raise ValueError("orientation inconnue")
    if o.aspect not in ASPECT_MODES:
        raise ValueError("mode d'image inconnu")
    if o.gain <= 0 or o.gain > 16:
        raise ValueError("gain audio entre 0 et 16")


def amv_size_warning(w, h):
    """Les tables de AMV_EncDLL.dll ne gèrent que certaines tailles : hors table, l'encodeur d'origine produit une vidéo VIDE."""
    if w not in (96, 128, 160, 176, 192, 208, 320) or h not in (64, 96, 120, 128, 144, 160, 240, 288, 480, 600, 768, 960):
        return ("taille %dx%d hors des tables de l'encodeur AMV d'origine (qui produirait des images vides) ; "
                "ce programme l'encode normalement, mais la lecture sur appareil n'est pas garantie" % (w, h))
    return ""


def default_output_path(src, o):
    base = os.path.splitext(os.path.basename(src))[0] + "." + o.fmt
    d = o.outdir or os.path.dirname(os.path.abspath(src))
    return os.path.join(d, base)


def avi_idx1(entries):
    """entries : liste de (tag, taille_complétée). Offsets depuis 'movi' (premier chunk = 4)."""
    off = 4
    body = bytearray()
    for tag, padded in entries:
        body += tag + _struct.pack('<III', 0x10, off, padded)
        off += 8 + padded
    return b'idx1' + _struct.pack('<I', len(body)) + bytes(body)


def convert_file(src, dst, o, progress=None, cancel=None, log=None):
    """Convertit src -> dst (AMV ou AVI). progress(fraction, texte) ; cancel : threading.Event ; log(texte)."""
    t0 = time.time()
    log = log or (lambda m: None)
    validate_options(o)
    if os.path.exists(dst) and not o.overwrite:
        raise FileExistsError(dst)
    temps = []
    vr = ar = None
    part = dst + ".part"
    try:
        real_src = src
        if src.lower().endswith(".amv"):
            log("Source AMV : décodage interne (les tables du décodeur officiel diffèrent de celles de ffmpeg)")
            real_src = export_amv_to_temp(src)
            temps.append(real_src)
        info = probe(real_src)
        if not info.has_video:
            raise ToolError("aucune piste vidéo dans %s" % src)
        total = info.duration
        start = max(0.0, o.start)
        end = o.end if (o.end and o.end > start) else total
        if total:
            end = min(end, total)
        dur = end - start
        if dur <= 0.05:
            raise ValueError("durée à convertir nulle (début/fin incohérents)")
        orient = o.orientation
        if o.vendor_updown_quirk and orient == "flipv":
            orient = "rot180"
        # --- cadence et audio
        if o.fmt == "amv":
            fps_exp = str(int(o.fps))
            fps_eff = float(int(o.fps))
            spb = 0
            w = amv_size_warning(o.width, o.height)
            if w:
                log("ATTENTION : " + w)
        else:
            spb = avi_samples_per_block(int(o.fps))
            fps_exp = "%d/%d" % (AVI_AUDIO_RATE, spb)
            fps_eff = AVI_AUDIO_RATE / spb
            log("AVI : %d échantillons audio par image => cadence réelle %.3f i/s" % (spb, fps_eff))
        nframes = max(1, int(round(dur * fps_eff)))
        if o.fmt == "amv":
            # Le décodeur officiel (et le convertisseur d'origine, qui encode « une seconde à la fois ») attendent un nombre
            # ENTIER de secondes : la dernière seconde incomplète est complétée (images noires + silence, option Insertpic/Insertwave)
            # si elle dépasse 1/4 de seconde, sinon abandonnée.
            fpsi = int(o.fps)
            partial = nframes % fpsi
            if partial:
                if (o.insertpic or o.insertwave) and partial >= max(1, fpsi // 4):
                    nframes += fpsi - partial
                else:
                    nframes -= partial
            if nframes <= 0:
                nframes = fpsi
        ainfo = probe(o.audio_file) if o.audio_file else info
        if ainfo.has_audio:
            ach = 1 if ainfo.achannels == 1 else 2
            arate = ainfo.arate if ainfo.arate >= 4000 else 44100
            a_start = 0.0 if o.audio_file else start
            ar = FFAudioReader(o.audio_file or real_src, arate, ach, a_start, dur + 0.5)
        else:
            ach, arate = 1, AVI_AUDIO_RATE
            ar = SilentAudio(1)
            log("Pas de piste audio : silence inséré")
        vf = build_video_filter(orient, o.aspect, o.width, o.height, fps_exp)
        vr = FFVideoReader(real_src, vf, o.width, o.height, start, dur + 0.5)
        black = np.zeros((o.height, o.width, 3), np.uint8)
        os.makedirs(os.path.dirname(os.path.abspath(dst)) or ".", exist_ok=True)
        fh = open(part, "wb")
        try:
            if o.fmt == "amv":
                audio_enc = AmvAudioEncoder(arate, ach, o.audio_rate)
                out_rate = audio_enc.out_rate
                fh.write(bytes(AMV_HEADER_SIZE))
                sizes = []
                movi = 0
                per = arate // int(o.fps)
            else:
                adpcm = ImaAdpcmWavEncoder(low_nibble_first=True)
                mono = AudioMonoResampler(arate, ach, AVI_AUDIO_RATE)
                fifo = []
                fh.write(bytes(328))
                entries = []
                movi = 0
                src_pos = 0
            done = 0
            last_report = 0.0
            movi_box = [0]

            def emit(k, frame, pcm):
                """Encode et écrit l'image k et son bloc audio (pcm : liste d'entiers)."""
                if o.fmt == "amv":
                    vchunk = encode_frame(frame)
                    achunk = audio_enc.block(pcm)
                    for tag, payload in ((b"00dc", vchunk), (b"01wb", achunk)):
                        fh.write(tag + _struct.pack("<I", len(payload)) + payload)
                        sizes.append((tag, len(payload)))
                        movi_box[0] += 8 + len(payload)
                else:
                    fifo.extend(mono.feed(pcm))
                    if len(fifo) < spb:
                        fifo.extend([0] * (spb - len(fifo)))
                    block = fifo[:spb]
                    del fifo[:spb]
                    vchunk = encode_frame_avi(frame)
                    achunk = adpcm.block(block)
                    for tag, payload in ((b"00dc", vchunk), (b"01wb", achunk)):
                        padded = (len(payload) + 3) & ~3
                        fh.write(tag + _struct.pack("<I", len(payload)) + payload + bytes(padded - len(payload)))
                        entries.append((tag, padded))
                        movi_box[0] += 8 + padded

            def samples_for(k):
                nonlocal src_pos
                if o.fmt == "amv":
                    f = k % int(o.fps)
                    return per if f < int(o.fps) - 1 else arate - (int(o.fps) - 1) * per
                nxt = ((k + 1) * spb * arate) // AVI_AUDIO_RATE
                n = nxt - src_pos
                src_pos = nxt
                return n

            fifo = []
            src_pos = 0
            for k in range(nframes):
                if cancel is not None and cancel.is_set():
                    raise Cancelled()
                frame = vr.read()
                if frame is None:
                    if not o.insertpic and o.fmt != "amv":
                        log("Fin de la vidéo à l'image %d (Insertpic désactivé)" % k)
                        break
                    frame = black
                if o.rgb565:
                    frame = to_rgb565(frame)
                n = samples_for(k)
                pcm = ar.read(n)
                if pcm.size < n * ach:
                    if not o.insertwave and o.fmt != "amv" and ar.eof and pcm.size == 0 and not isinstance(ar, SilentAudio):
                        log("Fin de l'audio à l'image %d (Insertwave désactivé)" % k)
                        break
                    pcm = np.concatenate([pcm, np.zeros(n * ach - pcm.size, "<i2")])
                emit(k, frame, apply_gain(pcm, o.gain).astype(np.int64).tolist())
                done += 1
                now = time.time()
                if progress and now - last_report > 0.15:
                    last_report = now
                    progress(done / nframes, "%d / %d images" % (done, nframes))
            if o.fmt == "amv" and done and done % int(o.fps):
                # garantit un nombre entier de secondes même si la source s'est arrêtée plus tôt
                for k in range(done, done + int(o.fps) - done % int(o.fps)):
                    emit(k, black, [0] * (samples_for(k) * ach))
                    done += 1
            movi = movi_box[0]
            if done == 0:
                raise ToolError("aucune image convertie")
            seconds = int(round(done / fps_eff))
            if o.fmt == "amv":
                fh.write(b"AMV_END_")
                fh.write(amv_idx1(sizes))
                fh.seek(0)
                fh.write(amv_header(o.width, o.height, int(o.fps), out_rate, movi, seconds))
            else:
                idx = avi_idx1(entries)
                fh.write(idx)
                fh.seek(0)
                fh.write(avi_header(o.width, o.height, done, spb, movi, len(idx), seconds))
        finally:
            fh.close()
        os.replace(part, dst)
        if progress:
            progress(1.0, "terminé")
        return {"frames": done, "seconds": done / fps_eff, "bytes": os.path.getsize(dst), "elapsed": time.time() - t0, "fps": fps_eff}
    except BaseException:
        try:
            if os.path.exists(part):
                os.remove(part)
        except OSError:
            pass
        raise
    finally:
        for r in (vr, ar):
            if r is not None:
                r.close()
        for t in temps:
            try:
                os.remove(t)
            except OSError:
                pass



# ============================================================================================
# LECTURE DES FICHIERS AMV / AVI (décodeur identique au décodeur officiel AMV_DecDLL.dll)
# ============================================================================================
import wave


class MediaFileError(Exception):
    pass


def _u32(b, o):
    return _struct.unpack_from("<I", b, o)[0]


class _BaseFile:
    kind = ""

    def __init__(self, path):
        self.path = path
        self.video = []        # (offset, taille) des chunks 00dc
        self.audio = []        # (offset, taille) des chunks 01wb
        self.width = self.height = 0
        self.fps = 0.0
        self.audio_rate = 22050
        self.duration_header = 0
        self.has_idx1 = False
        self.has_end_marker = False
        self.data = b""

    @property
    def nframes(self):
        return len(self.video)

    @property
    def duration(self):
        return self.nframes / self.fps if self.fps else 0.0

    def chunk(self, lst, i):
        o, n = lst[i]
        return self.data[o:o + n]

    def audio_pcm(self, i0=0, i1=None):
        raise NotImplementedError

    def frame_rgb(self, i):
        raise NotImplementedError


class AmvFile(_BaseFile):
    kind = "amv"
    HEADER = 0x13C

    def __init__(self, path):
        super().__init__(path)
        with open(path, "rb") as f:
            self.data = f.read()
        b = self.data
        if len(b) < self.HEADER or b[0:4] != b"RIFF" or b[8:12] != b"AMV " or b[24:28] != b"amvh":
            raise MediaFileError("ce n'est pas un fichier AMV (en-tête RIFF/AMV absent)")
        self.usec = _u32(b, 0x20)
        self.width = _u32(b, 0x40)
        self.height = _u32(b, 0x44)
        self.fps = float(_u32(b, 0x48)) or (1e6 / self.usec if self.usec else 0.0)
        self.duration_header = b[0x54] + 60 * b[0x55] + 3600 * _struct.unpack_from("<H", b, 0x56)[0]
        self.audio_rate = _u32(b, 0x120)
        self.movi_list_size = _u32(b, 0x134)
        self.riff_size = _u32(b, 4)
        pos = self.HEADER
        n = len(b)
        while pos + 8 <= n:
            tag = b[pos:pos + 4]
            if tag == b"AMV_":
                self.has_end_marker = b[pos:pos + 8] == b"AMV_END_"
                if pos + 16 <= n and b[pos + 8:pos + 12] == b"idx1":
                    self.has_idx1 = True
                break
            if tag not in (b"00dc", b"01wb"):
                break
            size = _u32(b, pos + 4)
            if pos + 8 + size > n:
                break
            (self.video if tag == b"00dc" else self.audio).append((pos + 8, size))
            pos += 8 + size
        self.end_pos = pos

    def frame_bgr_dib(self, i):
        return decode_frame_bgr(self.chunk(self.video, i), self.width, self.height)

    def frame_rgb(self, i):
        """Image visible (haut en premier), RGB."""
        return np.ascontiguousarray(self.frame_bgr_dib(i)[::-1, :, ::-1])

    def audio_pcm(self, i0=0, i1=None):
        i1 = len(self.audio) if i1 is None else min(i1, len(self.audio))
        parts = [np.array(ImaAdpcmAmvDecoder.block(self.chunk(self.audio, i)), dtype=np.int16) for i in range(i0, i1)]
        return np.concatenate(parts) if parts else np.zeros(0, np.int16)


class AviFile(_BaseFile):
    kind = "avi"
    HEADER = 0x148

    def __init__(self, path):
        super().__init__(path)
        with open(path, "rb") as f:
            self.data = f.read()
        b = self.data
        if len(b) < self.HEADER or b[0:4] != b"RIFF" or b[8:12] != b"AVI " or b[0x18:0x1c] != b"avih":
            raise MediaFileError("ce n'est pas un AVI produit par ce convertisseur")
        self.usec = _u32(b, 0x20)
        self.width = _u32(b, 0x40)
        self.height = _u32(b, 0x44)
        self.fps = 1e6 / self.usec if self.usec else 0.0
        self.duration_header = _u32(b, 0x54)
        self.audio_rate = _u32(b, 0x12C)
        self.spb = _struct.unpack_from("<H", b, 0x13A)[0]
        if b[0x74:0x78] != b"MJPG" and b[0x70:0x74] != b"MJPG":
            raise MediaFileError("seul le MJPEG (AVI du convertisseur) est pris en charge par le lecteur interne")
        pos = self.HEADER
        n = len(b)
        while pos + 8 <= n:
            tag = b[pos:pos + 4]
            if tag == b"idx1":
                self.has_idx1 = True
                break
            if tag not in (b"00dc", b"01wb"):
                break
            size = _u32(b, pos + 4)
            if pos + 8 + size > n:
                break
            (self.video if tag == b"00dc" else self.audio).append((pos + 8, size))
            pos += 8 + ((size + 3) & ~3)
        self.end_pos = pos

    def frame_rgb(self, i):
        return np.ascontiguousarray(decode_avi_frame_bgr(self.chunk(self.video, i), self.width, self.height)[:, :, ::-1])

    def frame_bgr_dib(self, i):
        return np.ascontiguousarray(decode_avi_frame_bgr(self.chunk(self.video, i), self.width, self.height)[::-1])

    def audio_pcm(self, i0=0, i1=None):
        i1 = len(self.audio) if i1 is None else min(i1, len(self.audio))
        parts = [np.array(ImaAdpcmWavDecoder.block(self.chunk(self.audio, i), self.spb), dtype=np.int16) for i in range(i0, i1)]
        return np.concatenate(parts) if parts else np.zeros(0, np.int16)


def open_media(path):
    with open(path, "rb") as f:
        head = f.read(16)
    if head[8:12] == b"AMV ":
        return AmvFile(path)
    if head[8:12] == b"AVI ":
        return AviFile(path)
    raise MediaFileError("format non reconnu (AMV ou AVI du convertisseur attendu)")


def write_wav(path, pcm, rate):
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(np.asarray(pcm, "<i2").tobytes())


def file_properties(m):
    """Dictionnaire de propriétés (équivalent de la boîte « Property » du lecteur d'origine)."""
    d = {
        "Format": m.kind.upper(),
        "Taille de l'image": "%d x %d" % (m.width, m.height),
        "Images par seconde": "%.3f" % m.fps,
        "Nombre d'images": str(m.nframes),
        "Durée (mesurée)": "%.2f s" % m.duration,
        "Durée (en-tête)": "%d s" % m.duration_header,
        "Fréquence audio": "%d Hz (mono, ADPCM IMA)" % m.audio_rate,
        "Blocs audio": str(len(m.audio)),
        "Taille du fichier": "%d octets" % len(m.data),
    }
    if m.nframes:
        d["Débit moyen"] = "%.0f ko/s" % (len(m.data) / max(m.duration, 1e-9) / 1000)
    if m.kind == "avi":
        d["Échantillons audio par bloc"] = str(m.spb)
    return d


def verify_file(path):
    """Vérifie la structure d'un fichier AMV/AVI du convertisseur. Retourne (ok, [messages])."""
    msgs = []
    ok = True
    try:
        m = open_media(path)
    except Exception as e:
        return False, ["ERREUR : %s" % e]
    msgs.append("Format %s, %dx%d, %.3f i/s, %d images, %d blocs audio" % (m.kind.upper(), m.width, m.height, m.fps, m.nframes, len(m.audio)))
    if m.nframes == 0:
        return False, msgs + ["ERREUR : aucune image"]
    if len(m.video) != len(m.audio):
        ok = False
        msgs.append("ERREUR : %d images pour %d blocs audio (entrelacement V,A attendu)" % (len(m.video), len(m.audio)))
    if m.width % 16:
        msgs.append("AVERTISSEMENT : largeur non multiple de 16")
    if m.kind == "amv":
        if not m.has_end_marker:
            ok = False
            msgs.append("ERREUR : marqueur AMV_END_ absent")
        if not m.has_idx1:
            msgs.append("AVERTISSEMENT : index idx1 absent (le convertisseur d'origine en écrit un)")
        payload = sum(8 + n for _o, n in m.video) + sum(8 + n for _o, n in m.audio)
        if m.movi_list_size != 12 + payload:
            msgs.append("AVERTISSEMENT : taille de LIST movi %d ≠ 12 + chunks (%d)" % (m.movi_list_size, 12 + payload))
        if m.riff_size not in (0,):
            msgs.append("information : taille RIFF = %d (le convertisseur d'origine écrit 0)" % m.riff_size)
        sample_total = 0
        for i in range(len(m.audio)):
            c = m.chunk(m.audio, i)
            if len(c) < 8:
                ok = False
                msgs.append("ERREUR : bloc audio %d trop court" % i)
                break
            pred, idx, _p, nsamp = _struct.unpack("<hBBI", c[:8])
            if idx > 88 or len(c) != 8 + (nsamp + 1) // 2:
                ok = False
                msgs.append("ERREUR : bloc audio %d incohérent (index %d, %d échantillons, %d octets)" % (i, idx, nsamp, len(c)))
                break
            sample_total += nsamp
        else:
            msgs.append("Audio : %d échantillons (%.2f s à %d Hz)" % (sample_total, sample_total / max(m.audio_rate, 1), m.audio_rate))
    else:
        if not m.has_idx1:
            ok = False
            msgs.append("ERREUR : index idx1 absent")
    try:
        m.frame_rgb(0)
        m.frame_rgb(m.nframes - 1)
        msgs.append("Décodage de la première et de la dernière image : OK")
    except Exception as e:
        ok = False
        msgs.append("ERREUR de décodage : %s" % e)
    if abs(m.duration - m.duration_header) > 1.5:
        msgs.append("AVERTISSEMENT : durée de l'en-tête (%d s) ≠ durée mesurée (%.1f s)" % (m.duration_header, m.duration))
    msgs.append("Structure %s" % ("VALIDE" if ok else "INVALIDE"))
    return ok, msgs


def export_to_video(src, dst, progress=None, cancel=None, log=None):
    """Décode un AMV/AVI avec le décodeur interne et encode vers dst (mp4/avi/mkv…) via ffmpeg."""
    log = log or (lambda m: None)
    m = open_media(src)
    ffmpeg = require_tool("ffmpeg")
    tmpd = tempfile.mkdtemp(prefix="mpu_")
    wav = os.path.join(tmpd, "a.wav")
    try:
        write_wav(wav, m.audio_pcm(), m.audio_rate)
        ext = os.path.splitext(dst)[1].lower()
        attempts = []
        if ext in (".mp4", ".mkv", ".mov"):
            attempts.append(["-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "20", "-c:a", "aac"])
        attempts.append(["-c:v", "mpeg4", "-q:v", "2", "-pix_fmt", "yuv420p", "-c:a", "pcm_s16le" if ext in (".avi", ".mkv") else "aac"])
        last_err = ""
        for enc in attempts:
            cmd = [ffmpeg, "-y", "-hide_banner", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "bgr24",
                   "-s", "%dx%d" % (m.width, m.height), "-r", "%.6f" % m.fps, "-i", "-", "-i", wav] + enc + ["-shortest", dst]
            p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stderr=subprocess.PIPE, **_NO_WINDOW)
            try:
                for i in range(m.nframes):
                    if cancel is not None and cancel.is_set():
                        p.kill()
                        raise Cancelled()
                    fr = m.frame_bgr_dib(i)[::-1] if m.kind == "amv" else decode_avi_frame_bgr(m.chunk(m.video, i), m.width, m.height)
                    p.stdin.write(np.ascontiguousarray(fr).tobytes())
                    if progress and i % 8 == 0:
                        progress(i / m.nframes, "%d / %d" % (i, m.nframes))
                p.stdin.close()
            except BrokenPipeError:
                pass
            err = p.stderr.read().decode("utf-8", "replace")
            p.wait()
            if p.returncode == 0:
                if progress:
                    progress(1.0, "terminé")
                return {"frames": m.nframes, "bytes": os.path.getsize(dst)}
            last_err = err
        raise ToolError("ffmpeg a échoué : %s" % last_err.strip()[-300:])
    finally:
        shutil.rmtree(tmpd, ignore_errors=True)


def export_amv_to_temp(src):
    fd, path = tempfile.mkstemp(prefix="mpu_src_", suffix=".avi")
    os.close(fd)
    export_to_video(src, path)
    return path


def extract_frame(m, i, dst):
    """Enregistre l'image i (PNG sans dépendance externe, ou BMP selon l'extension)."""
    rgb = m.frame_rgb(i)
    ext = os.path.splitext(dst)[1].lower()
    if ext == ".bmp":
        h, w, _ = rgb.shape
        row = (w * 3 + 3) & ~3
        pad = row - w * 3
        bgr = rgb[::-1, :, ::-1]
        body = b"".join(bytes(r.tobytes()) + bytes(pad) for r in bgr)
        hdr = b"BM" + _struct.pack("<IHHI", 54 + len(body), 0, 0, 54) + _struct.pack("<IiiHHIIiiII", 40, w, h, 1, 24, 0, len(body), 2835, 2835, 0, 0)
        with open(dst, "wb") as f:
            f.write(hdr + body)
    else:
        import zlib
        h, w, _ = rgb.shape
        raw = b"".join(b"\x00" + rgb[y].tobytes() for y in range(h))

        def chunk(t, d):
            c = _struct.pack(">I", len(d)) + t + d
            return c + _struct.pack(">I", zlib.crc32(t + d) & 0xFFFFFFFF)
        png = b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", _struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0)) + chunk(b"IDAT", zlib.compress(raw, 6)) + chunk(b"IEND", b"")
        with open(dst, "wb") as f:
            f.write(png)



# ============================================================================================
# OUTILS ANNEXES : téléchargeur (MediaGet), lecteur multimédia connecté (copie), lecture audio
# ============================================================================================
MEDIA_LINK_RE = re.compile(r"""(?:href|src|data-src|file|url)\s*[=:]\s*["']([^"'<>\s]+?\.(?:mp4|flv|avi|wmv|mkv|mov|mpg|mpeg|3gp|rmvb|rm|asf|webm|m4v|mp3|wav)(?:\?[^"'<>\s]*)?)["']""", re.I)


def find_media_links(page_url, timeout=15):
    """Équivalent simplifié du module « grab » (grabcom.ocx) : repère les liens vers des fichiers multimédias d'une page web."""
    req = urllib.request.Request(page_url, headers={"User-Agent": "Mozilla/5.0 (mpu_toolkit)"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        html = r.read(4_000_000).decode("utf-8", "replace")
    out = []
    for m in MEDIA_LINK_RE.finditer(html):
        u = urllib.parse.urljoin(page_url, m.group(1).replace("\\/", "/"))
        if u not in out:
            out.append(u)
    return out


class DownloadItem:
    def __init__(self, url, dest_dir):
        self.url = url
        name = os.path.basename(urllib.parse.urlparse(url).path) or "media.bin"
        self.name = urllib.parse.unquote(name)
        self.path = os.path.join(dest_dir, self.name)
        self.size = 0
        self.done = 0
        self.speed = 0.0
        self.state = "ready"       # ready | downloading | success | error | stopped
        self.error = ""
        self.cancel = threading.Event()


def download(item, progress=None):
    """Télécharge item.url vers item.path (écriture dans un fichier .part)."""
    item.state = "downloading"
    item.cancel.clear()
    t0 = time.time()
    try:
        req = urllib.request.Request(item.url, headers={"User-Agent": "Mozilla/5.0 (mpu_toolkit)"})
        with urllib.request.urlopen(req, timeout=20) as r:
            item.size = int(r.headers.get("Content-Length", 0) or 0)
            part = item.path + ".part"
            with open(part, "wb") as f:
                while True:
                    if item.cancel.is_set():
                        item.state = "stopped"
                        break
                    buf = r.read(65536)
                    if not buf:
                        break
                    f.write(buf)
                    item.done += len(buf)
                    item.speed = item.done / max(time.time() - t0, 1e-6)
                    if progress:
                        progress(item)
        if item.state == "downloading":
            os.replace(part, item.path)
            item.state = "success"
        else:
            try:
                os.remove(part)
            except OSError:
                pass
    except Exception as e:                                  # réseau : toute erreur est affichée à l'utilisateur
        item.state = "error"
        item.error = str(e)
    if progress:
        progress(item)
    return item


def list_drives(include_fixed=False):
    """Lecteurs amovibles (clés USB, lecteurs MP3/MP4 en stockage de masse) : [{path, label, total, free}]."""
    drives = []
    if os.name == "nt":
        try:
            import ctypes
            mask = ctypes.windll.kernel32.GetLogicalDrives()
            for i in range(26):
                if mask & (1 << i):
                    root = "%s:\\" % chr(65 + i)
                    t = ctypes.windll.kernel32.GetDriveTypeW(root)
                    if t == 2 or (include_fixed and t == 3):
                        drives.append(root)
        except Exception:
            pass
    else:
        roots = []
        try:
            with open("/proc/mounts") as f:
                for ln in f:
                    p = ln.split()[1].replace("\\040", " ")
                    if p.startswith(("/media/", "/run/media/", "/mnt/", "/Volumes/")):
                        roots.append(p)
        except OSError:
            if os.path.isdir("/Volumes"):
                roots = [os.path.join("/Volumes", d) for d in os.listdir("/Volumes")]
        drives = [r for r in roots if os.path.isdir(r) and os.access(r, os.W_OK)]
    out = []
    for d in drives:
        try:
            u = shutil.disk_usage(d)
            out.append({"path": d, "label": d, "total": u.total, "free": u.free})
        except OSError:
            pass
    return out


def copy_to_device(src, dest_dir, delete_after=False, progress=None):
    """Copie un fichier vers le lecteur ; refuse si l'espace libre est insuffisant (message d'origine « Disk is full… »)."""
    size = os.path.getsize(src)
    free = shutil.disk_usage(dest_dir).free
    if size > free:
        raise OSError("Disque plein : %d Mo nécessaires, %d Mo libres" % (size // 2**20 + 1, free // 2**20))
    dst = os.path.join(dest_dir, os.path.basename(src))
    with open(src, "rb") as fi, open(dst, "wb") as fo:
        done = 0
        while True:
            buf = fi.read(1 << 20)
            if not buf:
                break
            fo.write(buf)
            done += len(buf)
            if progress:
                progress(done / max(size, 1))
    if delete_after:
        os.remove(src)
    return dst


def fmt_size(n):
    units = ("o", "Ko", "Mo", "Go", "To") if globals().get("LANG", "fr") == "fr" else ("B", "KB", "MB", "GB", "TB")
    for k, unit in enumerate(units):
        if n < 1024 or k == len(units) - 1:
            return ("%d %s" % (n, unit)) if k == 0 else ("%.1f %s" % (n, unit))
        n /= 1024.0


def fmt_time(sec):
    sec = max(0, int(sec))
    return "%02d:%02d:%02d" % (sec // 3600, (sec // 60) % 60, sec % 60) if sec >= 3600 else "%02d:%02d" % (sec // 60, sec % 60)


def parse_time(text):
    """« 90 », « 1:30 », « 01:02:03.5 » -> secondes (0 si vide)."""
    text = (text or "").strip()
    if not text:
        return 0.0
    parts = text.split(":")
    if len(parts) > 3:
        raise ValueError("durée invalide : %s" % text)
    total = 0.0
    for p in parts:
        total = total * 60 + float(p.replace(",", "."))
    return total


class AudioPlayer:
    """Lecture audio du lecteur interne : segments WAV de ~8 s rendus à la volée, lus par winsound / afplay / ffplay / paplay / aplay."""
    SEG = 8.0

    def __init__(self, media):
        self.m = media
        self.stop_flag = threading.Event()
        self.thread = None
        self.proc = None
        self.tmp = tempfile.mkdtemp(prefix="mpu_audio_")
        self.backend = self.detect()

    @staticmethod
    def detect():
        if os.name == "nt":
            try:
                import winsound  # noqa: F401  (simple test de disponibilité)
                return "winsound"
            except ImportError:
                pass
        for name, cmd in (("afplay", ["afplay"]), ("paplay", ["paplay"]), ("aplay", ["aplay", "-q"]), ("ffplay", ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet"])):
            if find_tool(name):
                return name
        return None

    def available(self):
        return self.backend is not None

    def _play_file(self, path, dur):
        if self.backend == "winsound":
            import winsound
            winsound.PlaySound(path, winsound.SND_FILENAME | winsound.SND_ASYNC)
            end = time.time() + dur
            while time.time() < end and not self.stop_flag.is_set():
                time.sleep(0.02)
            return
        cmds = {"afplay": ["afplay"], "paplay": ["paplay"], "aplay": ["aplay", "-q"],
                "ffplay": ["ffplay", "-nodisp", "-autoexit", "-loglevel", "quiet"]}
        exe = find_tool(self.backend) or self.backend
        self.proc = subprocess.Popen([exe] + cmds[self.backend][1:] + [path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, **_NO_WINDOW)
        while self.proc.poll() is None and not self.stop_flag.is_set():
            time.sleep(0.02)
        if self.proc.poll() is None:
            self.proc.kill()

    def start(self, frame_index):
        self.stop()
        if not self.available() or not self.m.audio:
            return
        self.stop_flag.clear()
        self.thread = threading.Thread(target=self._run, args=(frame_index,), daemon=True)
        self.thread.start()

    def _run(self, frame_index):
        fps = self.m.fps
        seg_frames = max(1, int(self.SEG * fps))
        i = frame_index
        n = len(self.m.audio)
        k = 0
        while i < n and not self.stop_flag.is_set():
            j = min(n, i + seg_frames)
            pcm = self.m.audio_pcm(i, j)
            path = os.path.join(self.tmp, "seg%d.wav" % (k % 2))
            write_wav(path, pcm, self.m.audio_rate)
            self._play_file(path, len(pcm) / float(self.m.audio_rate))
            i = j
            k += 1

    def stop(self):
        self.stop_flag.set()
        if self.backend == "winsound":
            try:
                import winsound
                winsound.PlaySound(None, winsound.SND_PURGE)
            except Exception:
                pass
        if self.proc is not None and self.proc.poll() is None:
            try:
                self.proc.kill()
            except Exception:
                pass
        if self.thread is not None and self.thread.is_alive():
            self.thread.join(timeout=1.0)

    def cleanup(self):
        self.stop()
        shutil.rmtree(self.tmp, ignore_errors=True)



# ============================================================================================
# LANGUES ET RÉGLAGES (settings.ini au format du convertisseur d'origine + section [Toolkit])
# ============================================================================================
import locale

LANG = "fr"

_FR = {
    "tab_convert": "Convertir", "tab_player": "Lecteur", "tab_tools": "Outils", "tab_mediaget": "MediaGet", "tab_about": "À propos",
    "menu_file": "Fichier", "menu_view": "Affichage", "menu_help": "Aide", "quit": "Quitter",
    "restart_needed": "Le changement de langue sera appliqué au prochain démarrage.",
    "col_name": "Fichier", "col_info": "Informations", "col_status": "État",
    "add_files": "Ajouter des fichiers…", "add_folder": "Ajouter un dossier…", "remove": "Retirer", "clear": "Tout effacer",
    "grp_output": "Sortie", "grp_image": "Image et son", "format": "Format", "size": "Taille de l'image", "custom_size": "Personnalisée :",
    "tip_custom": "Largeur multiple de 16, hauteur multiple de 8. Hors des tailles du convertisseur d'origine, l'encodeur AMV d'origine produisait\ndes images vides ; ce programme les encode normalement mais la lecture sur appareil n'est pas garantie.",
    "fps": "Images par seconde", "fps_unit": "images/s", "fps_avi_note": "AVI : cadence réelle %.2f images/s (imposée par la durée du bloc audio)",
    "audio_rate": "Fréquence audio (AMV)", "out_dir": "Dossier de sortie", "tip_outdir": "Vide = même dossier que le fichier source",
    "overwrite": "Écraser les fichiers existants", "play_after": "Lire après la conversion", "copy_to": "Copier vers le lecteur :",
    "delete_after": "Supprimer le fichier converti après la copie", "no_device": "(aucun lecteur détecté)",
    "total": "Total", "free": "Libre", "used": "Utilisé",
    "orientation": "Orientation", "aspect": "Mode d'image",
    "orient_normal": "Normale", "orient_flipv": "Haut-bas", "orient_fliph": "Gauche-droite", "orient_rot180": "Haut-bas + gauche-droite (180°)",
    "orient_rot90cw": "Rotation 90° horaire", "orient_rot90ccw": "Rotation 90° anti-horaire",
    "aspect_stretch": "Étirer (comportement d'origine)", "aspect_letterbox": "Conserver le ratio (bandes noires)", "aspect_crop": "Conserver le ratio (recadrer)",
    "tip_aspect": "Le chemin FFmpeg du programme d'origine étire toujours l'image à la taille choisie (mesuré). Les deux autres modes sont des ajouts.",
    "cut": "Découper", "cut_start": "de", "cut_end": "à", "tip_cut": "Secondes ou mm:ss ou hh:mm:ss ; vide = début / fin de la vidéo",
    "audio_file": "Remplacer la piste audio", "gain": "Gain audio", "rgb565": "Espace couleur 16 bits (RGB565)",
    "insertwave": "Compléter l'audio manquant (silence)", "insertpic": "Compléter l'image manquante (noir)",
    "vendor_quirk": "Reproduire le défaut d'origine : « Haut-bas » = rotation 180°",
    "tip_quirk": "Dans le chemin FFmpeg d'origine, l'option « UpDown » fait en réalité tourner l'image de 180° (mesuré). Décoché : vrai retournement vertical.",
    "start": "Démarrer", "stop": "Arrêter", "ready": "Prêt", "stopping": "Arrêt en cours…", "finished": "Terminé",
    "ft_video": "Vidéos", "ft_audio": "Audio", "ft_all": "Tous les fichiers", "no_video": "aucune piste vidéo",
    "st_ready": "Prêt", "st_error": "Erreur", "st_waiting": "En attente", "st_converting": "Conversion…", "st_skipped": "Ignoré",
    "st_done": "Terminé", "st_cancelled": "Annulé",
    "err_fps": "Cadence invalide.", "nothing_to_do": "Aucun fichier à convertir : ajoutez des vidéos.",
    "no_ffmpeg": "ffmpeg / ffprobe introuvables. Installez ffmpeg (ffmpeg.org) puis placez-le dans le PATH ou choisissez son dossier dans « À propos ».",
    "log_start": "Conversion de %s → %s", "err_same_file": "Le fichier de sortie est identique au fichier source.",
    "ask_overwrite": "Le fichier %s existe déjà. Voulez-vous l'écraser ?",
    "log_done": "Terminé : %d images, %.1f s, %s, en %.1f s", "log_copied": "Copié vers %s", "err_copy": "Copie impossible : %s", "err_convert": "Erreur : %s",
    "pl_open": "Ouvrir…", "pl_prev": "Précédent", "pl_backward": "−5 s", "pl_play": "Lecture", "pl_pause": "Pause", "pl_forward": "+5 s", "pl_next": "Suivant",
    "pl_repeat": "Répéter", "pl_adjust": "Adapter à la fenêtre", "pl_amplify": "Agrandir", "pl_reduce": "Réduire", "pl_equal": "Taille réelle",
    "pl_property": "Propriétés", "pl_snapshot": "Capturer l'image", "pl_fullscreen": "Plein écran",
    "pl_noaudio": "pas de lecteur audio détecté (image seule)", "pl_noaudio_hint": "Espace : lecture/pause — ←/→ : ±5 s — F11 : plein écran",
    "pl_empty": "fichier sans image", "pl_saved": "Image enregistrée : %s",
    "browse": "Parcourir…", "tl_props": "Propriétés", "tl_verify": "Vérifier la structure", "tl_export": "Exporter en MP4…", "tl_wav": "Extraire l'audio (WAV)…",
    "tl_player": "Ouvrir dans le lecteur", "tl_frame": "Image n°", "tl_saveframe": "Enregistrer l'image…", "tl_choose": "Choisissez d'abord un fichier AMV/AVI.",
    "tl_exporting": "Export vers %s…", "tl_exported": "Export terminé : %d images, %s", "tl_saved": "Enregistré : %s",
    "mg_add": "Ajouter l'URL", "mg_scan": "Chercher les médias de la page", "mg_dir": "Dossier :", "mg_n": "N°", "mg_name": "Nom", "mg_size": "Taille",
    "mg_prog": "Avancement", "mg_speed": "Vitesse", "mg_state": "État", "mg_badurl": "Saisissez une adresse http:// ou https://", "mg_scanning": "Analyse de la page…",
    "mg_found": "%d lien(s) multimédia trouvé(s)", "mg_download": "Télécharger", "mg_stop": "Arrêter", "mg_delete": "Supprimer", "mg_sendconv": "Envoyer au convertisseur",
    "mg_state_ready": "Prêt", "mg_state_downloading": "Téléchargement", "mg_state_success": "Réussi", "mg_state_error": "Erreur", "mg_state_stopped": "Arrêté",
    "ab_pick_ffmpeg": "Choisir le dossier de ffmpeg…", "ab_refresh": "Actualiser", "ab_missing": "(introuvable)", "ab_noaudio": "(aucun : lecture sans son)",
    "about_text": (
        "%s  %s\nReconstruction de « %s » (Actions Semiconductor) — un seul fichier Python + Tkinter.\n\n"
        "Dépendances\n  ffmpeg : %s\n  version : %s\n  ffprobe : %s\n  lecture audio : %s\n  réglages : %s\n\n"
        "Ce qui est identique au programme d'origine (vérifié octet par octet contre les DLL d'origine sous Wine)\n"
        "  • encodeur AMV : couleur, DCT, quantification, Huffman, audio ADPCM IMA, rééchantillonnage, en-tête, index, AMV_END_\n"
        "  • encodeur AVI : JPEG MJPEG, ADPCM WAV (blocs de 1017 ou 1529 échantillons), en-tête, index\n"
        "  • décodeur AMV (IDCT, couleur, suréchantillonnage chroma particulier, ADPCM)\n\n"
        "Ce qui est un choix ou une hypothèse de ce programme (le convertisseur d'origine ne peut pas être exécuté sans MFC42.DLL)\n"
        "  • décodage des sources, redimensionnement, sélection des images : ffmpeg (au lieu de DirectShow / FFMpegDll)\n"
        "  • Insertwave / Insertpic, modes d'image, gain ACOE, RGB565, téléchargeur MediaGet, copie vers le lecteur, interface\n\n"
        "Défauts connus du programme d'origine, volontairement non reproduits : dernière seconde perdue (chemin FFmpeg), tailles hors table donnant une vidéo vide (208×176),\n"
        "rotations de 90° déformées. FFmpeg 6.1 décode mal les fichiers AMV de ce convertisseur (tables de quantification différentes) : utilisez le lecteur intégré.\n"),
}

_EN = {
    "tab_convert": "Convert", "tab_player": "Player", "tab_tools": "Tools", "tab_mediaget": "MediaGet", "tab_about": "About",
    "menu_file": "File", "menu_view": "View", "menu_help": "Help", "quit": "Quit",
    "restart_needed": "The language change will apply at next start.",
    "col_name": "File", "col_info": "Information", "col_status": "Status",
    "add_files": "Add files…", "add_folder": "Add folder…", "remove": "Remove", "clear": "Clear all",
    "grp_output": "Output", "grp_image": "Picture and sound", "format": "Format", "size": "Picture size", "custom_size": "Custom:",
    "tip_custom": "Width multiple of 16, height multiple of 8. Outside the original converter's sizes the original AMV encoder produced\nempty pictures; this program encodes them normally but playback on a device is not guaranteed.",
    "fps": "Frames per second", "fps_unit": "frames/s", "fps_avi_note": "AVI: real rate %.2f frames/s (set by the audio block duration)",
    "audio_rate": "Audio sample rate (AMV)", "out_dir": "Output folder", "tip_outdir": "Empty = same folder as the source file",
    "overwrite": "Overwrite existing files", "play_after": "Play after converting", "copy_to": "Copy to player:",
    "delete_after": "Delete the converted file after copying", "no_device": "(no player detected)",
    "total": "Total", "free": "Free", "used": "Used",
    "orientation": "Orientation", "aspect": "Picture mode",
    "orient_normal": "Normal", "orient_flipv": "Up-down", "orient_fliph": "Left-right", "orient_rot180": "Up-down + left-right (180°)",
    "orient_rot90cw": "Rotate 90° clockwise", "orient_rot90ccw": "Rotate 90° anticlockwise",
    "aspect_stretch": "Stretch (original behaviour)", "aspect_letterbox": "Keep ratio (black bars)", "aspect_crop": "Keep ratio (crop)",
    "tip_aspect": "The original program's FFmpeg path always stretches the picture to the chosen size (measured). The other two modes are additions.",
    "cut": "Cut", "cut_start": "from", "cut_end": "to", "tip_cut": "Seconds, mm:ss or hh:mm:ss; empty = start / end of the video",
    "audio_file": "Replace audio track", "gain": "Audio gain", "rgb565": "16-bit colour space (RGB565)",
    "insertwave": "Fill missing audio (silence)", "insertpic": "Fill missing picture (black)",
    "vendor_quirk": "Reproduce the original defect: “Up-down” = 180° rotation",
    "tip_quirk": "In the original FFmpeg path, the “UpDown” option actually rotates the picture by 180° (measured). Unchecked: a true vertical flip.",
    "start": "Start", "stop": "Stop", "ready": "Ready", "stopping": "Stopping…", "finished": "Finished",
    "ft_video": "Videos", "ft_audio": "Audio", "ft_all": "All files", "no_video": "no video track",
    "st_ready": "Ready", "st_error": "Error", "st_waiting": "Waiting", "st_converting": "Converting…", "st_skipped": "Skipped",
    "st_done": "Done", "st_cancelled": "Cancelled",
    "err_fps": "Invalid frame rate.", "nothing_to_do": "No file to convert: add some videos.",
    "no_ffmpeg": "ffmpeg / ffprobe not found. Install ffmpeg (ffmpeg.org), then put it in the PATH or choose its folder in “About”.",
    "log_start": "Converting %s → %s", "err_same_file": "The output file is the same as the source file.",
    "ask_overwrite": "The file %s already exists. Overwrite it?",
    "log_done": "Done: %d frames, %.1f s, %s, in %.1f s", "log_copied": "Copied to %s", "err_copy": "Copy failed: %s", "err_convert": "Error: %s",
    "pl_open": "Open…", "pl_prev": "Previous", "pl_backward": "−5 s", "pl_play": "Play", "pl_pause": "Pause", "pl_forward": "+5 s", "pl_next": "Next",
    "pl_repeat": "Repeat", "pl_adjust": "Fit to window", "pl_amplify": "Amplify", "pl_reduce": "Reduce", "pl_equal": "Actual size",
    "pl_property": "Property", "pl_snapshot": "Save picture", "pl_fullscreen": "Full screen",
    "pl_noaudio": "no audio player found (picture only)", "pl_noaudio_hint": "Space: play/pause — ←/→: ±5 s — F11: full screen",
    "pl_empty": "file without pictures", "pl_saved": "Picture saved: %s",
    "browse": "Browse…", "tl_props": "Properties", "tl_verify": "Check structure", "tl_export": "Export to MP4…", "tl_wav": "Extract audio (WAV)…",
    "tl_player": "Open in player", "tl_frame": "Frame #", "tl_saveframe": "Save picture…", "tl_choose": "Choose an AMV/AVI file first.",
    "tl_exporting": "Exporting to %s…", "tl_exported": "Export finished: %d frames, %s", "tl_saved": "Saved: %s",
    "mg_add": "Add URL", "mg_scan": "Find media on page", "mg_dir": "Folder:", "mg_n": "No.", "mg_name": "Name", "mg_size": "Size",
    "mg_prog": "Progress", "mg_speed": "Speed", "mg_state": "Status", "mg_badurl": "Enter an http:// or https:// address", "mg_scanning": "Scanning the page…",
    "mg_found": "%d media link(s) found", "mg_download": "Download", "mg_stop": "Stop", "mg_delete": "Delete", "mg_sendconv": "Send to converter",
    "mg_state_ready": "Ready", "mg_state_downloading": "Downloading", "mg_state_success": "Success", "mg_state_error": "Error", "mg_state_stopped": "Stopped",
    "ab_pick_ffmpeg": "Choose the ffmpeg folder…", "ab_refresh": "Refresh", "ab_missing": "(not found)", "ab_noaudio": "(none: silent playback)",
    "about_text": (
        "%s  %s\nReconstruction of “%s” (Actions Semiconductor) — a single Python + Tkinter file.\n\n"
        "Dependencies\n  ffmpeg: %s\n  version: %s\n  ffprobe: %s\n  audio playback: %s\n  settings: %s\n\n"
        "Identical to the original program (checked byte for byte against the original DLLs under Wine)\n"
        "  • AMV encoder: colour, DCT, quantisation, Huffman, IMA ADPCM audio, resampling, header, index, AMV_END_\n"
        "  • AVI encoder: MJPEG, WAV ADPCM (1017 or 1529 sample blocks), header, index\n"
        "  • AMV decoder (IDCT, colour, special chroma upsampling, ADPCM)\n\n"
        "Choices or assumptions of this program (the original converter cannot run without MFC42.DLL)\n"
        "  • source decoding, resizing, frame selection: ffmpeg (instead of DirectShow / FFMpegDll)\n"
        "  • Insertwave / Insertpic, picture modes, ACOE gain, RGB565, MediaGet downloader, copy to player, user interface\n\n"
        "Known defects of the original, deliberately not reproduced: last second lost (FFmpeg path), sizes outside the table giving an empty video (208×176),\n"
        "distorted 90° rotations. FFmpeg 6.1 decodes this converter's AMV files badly (different quantisation tables): use the built-in player.\n"),
}
STRINGS = {"fr": _FR, "en": _EN}


def _system_lang():
    for var in ("LC_ALL", "LC_MESSAGES", "LANG", "LANGUAGE"):
        v = os.environ.get(var, "")
        if v:
            return v.lower()
    try:
        import warnings
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            return (locale.getlocale()[0] or locale.getdefaultlocale()[0] or "").lower()
    except Exception:
        return ""


def set_lang(code):
    global LANG
    if code not in STRINGS:
        code = "fr" if _system_lang().startswith("fr") else "en"
    LANG = code


def T(key):
    return STRINGS.get(LANG, _EN).get(key) or _EN.get(key) or key


class Settings:
    """settings.ini : sections et clés du convertisseur d'origine ([TransformSetup], [PlayerSetup]) + section [Toolkit] propre à cet outil."""
    DEFAULTS = {
        "TransformSetup": {"Overwrite": "TRUE", "Insertwave": "FALSE", "Insertpic": "TRUE", "Transplay": "TRUE", "Trycode": "FALSE", "VFBS": "high",
                           "VWH": "3", "Imagequality": "0", "Imagezoom": "1", "Skin": "0", "CopyFile": "TRUE", "BMPADJUST": "0", "OUTPUTPATH": ""},
        "PlayerSetup": {"repeat": "TRUE", "adjust": "TRUE", "bmpdir": "0", "Skin": "0"},
        "Toolkit": {"Language": "auto", "Format": "amv", "Width": "160", "Height": "120", "CustomSize": "FALSE", "AudioRate": "22050",
                    "Orientation": "normal", "Aspect": "stretch", "Gain": "1.0", "RGB565": "FALSE", "DeleteAfterCopy": "FALSE",
                    "VendorUpDownQuirk": "FALSE", "FFmpegDir": ""},
    }

    def __init__(self, path=None):
        self.cp = configparser.ConfigParser(interpolation=None)
        self.cp.optionxform = str
        for sec, kv in self.DEFAULTS.items():
            self.cp[sec] = dict(kv)
        self.path = path or self._default_path()
        try:
            if os.path.isfile(self.path):
                self.cp.read(self.path, encoding="utf-8")
        except (OSError, configparser.Error):
            pass

    @staticmethod
    def _default_path():
        here = os.path.dirname(os.path.abspath(__file__)) if "__file__" in globals() else os.getcwd()
        if os.access(here, os.W_OK):
            return os.path.join(here, "settings.ini")
        d = os.path.join(os.path.expanduser("~"), ".mpu_toolkit")
        os.makedirs(d, exist_ok=True)
        return os.path.join(d, "settings.ini")

    def get(self, sec, key):
        return self.cp.get(sec, key, fallback=self.DEFAULTS.get(sec, {}).get(key, ""))

    def getbool(self, sec, key):
        return self.get(sec, key).strip().upper() in ("TRUE", "1", "YES", "ON")

    def set(self, sec, key, val):
        if not self.cp.has_section(sec):
            self.cp.add_section(sec)
        self.cp.set(sec, key, str(val))

    def save(self):
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                self.cp.write(f)
        except OSError:
            pass



# ============================================================================================
# INTERFACE GRAPHIQUE (Tkinter) — onglets : Convertir, Lecteur, Outils, MediaGet, À propos
# ============================================================================================
try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
    TK_OK = True
except Exception:                                    # Tkinter absent : seul le mode ligne de commande fonctionne
    tk = ttk = filedialog = messagebox = None
    TK_OK = False

SKINS = {
    "classic": {"bg": "#ece9d8", "fg": "#000000", "accent": "#316ac5", "field": "#ffffff", "bar": "#3a6ea5"},
    "ocean": {"bg": "#e3f0fa", "fg": "#0b2a3c", "accent": "#0b6fa4", "field": "#ffffff", "bar": "#0b8bbf"},
}


def apply_skin(root, name):
    sk = SKINS.get(name, SKINS["classic"])
    st = ttk.Style(root)
    try:
        st.theme_use("clam")
    except tk.TclError:
        pass
    root.configure(background=sk["bg"])
    st.configure(".", background=sk["bg"], foreground=sk["fg"], fieldbackground=sk["field"])
    st.configure("TLabelframe", background=sk["bg"])
    st.configure("TLabelframe.Label", background=sk["bg"], foreground=sk["accent"], font=("TkDefaultFont", 9, "bold"))
    st.configure("TNotebook", background=sk["bg"])
    st.configure("TNotebook.Tab", padding=(12, 4))
    st.map("TNotebook.Tab", background=[("selected", sk["field"])], foreground=[("selected", sk["accent"])])
    st.configure("TButton", padding=(8, 3))
    st.configure("Accent.TButton", background=sk["accent"], foreground="#ffffff", padding=(14, 5), font=("TkDefaultFont", 9, "bold"))
    st.map("Accent.TButton", background=[("active", sk["bar"]), ("disabled", "#9aa7b3")])
    st.configure("Horizontal.TProgressbar", background=sk["bar"], troughcolor="#cfd8df")
    st.configure("Treeview", rowheight=22, fieldbackground=sk["field"])
    st.configure("Treeview.Heading", font=("TkDefaultFont", 9, "bold"))
    return sk


class Tooltip:
    def __init__(self, widget, text):
        self.w, self.text, self.tip = widget, text, None
        widget.bind("<Enter>", self.show)
        widget.bind("<Leave>", self.hide)

    def show(self, _e=None):
        if self.tip or not self.text:
            return
        x = self.w.winfo_rootx() + 12
        y = self.w.winfo_rooty() + self.w.winfo_height() + 4
        self.tip = tk.Toplevel(self.w)
        self.tip.wm_overrideredirect(True)
        self.tip.wm_geometry("+%d+%d" % (x, y))
        tk.Label(self.tip, text=self.text, justify="left", background="#ffffe1", relief="solid", borderwidth=1, wraplength=380, padx=6, pady=3).pack()

    def hide(self, _e=None):
        if self.tip:
            self.tip.destroy()
            self.tip = None


def _first_drive_text(d):
    used = d["total"] - d["free"]
    return "%s  —  %s: %s  %s: %s  %s: %s" % (d["path"], T("total"), fmt_size(d["total"]), T("free"), fmt_size(d["free"]), T("used"), fmt_size(used))


class ConvertTab(ttk.Frame):
    """Onglet « Convertir » : équivalent de la fenêtre principale d'AMV/AVI Video Converter."""

    def __init__(self, master, app):
        super().__init__(master, padding=8)
        self.app = app
        s = app.settings
        self.files = []                      # dicts : path, info, status
        self.q = queue.Queue()
        self.cancel = threading.Event()
        self.worker = None
        self.drives = []
        # --- variables Tk (initialisées depuis settings.ini)
        self.v_fmt = tk.StringVar(value=s.get("Toolkit", "Format"))
        self.v_size = tk.StringVar()
        self.v_w = tk.IntVar(value=int(s.get("Toolkit", "Width")))
        self.v_h = tk.IntVar(value=int(s.get("Toolkit", "Height")))
        self.v_custom = tk.BooleanVar(value=s.getbool("Toolkit", "CustomSize"))
        self.v_fps = tk.StringVar()
        self.v_arate = tk.IntVar(value=int(s.get("Toolkit", "AudioRate")))
        self.v_orient = tk.StringVar()
        self.v_aspect = tk.StringVar()
        self.v_start = tk.StringVar(value="")
        self.v_end = tk.StringVar(value="")
        self.v_afile = tk.StringVar(value="")
        self.v_gain = tk.DoubleVar(value=float(s.get("Toolkit", "Gain")))
        self.v_565 = tk.BooleanVar(value=s.getbool("Toolkit", "RGB565"))
        self.v_iw = tk.BooleanVar(value=s.getbool("TransformSetup", "Insertwave"))
        self.v_ip = tk.BooleanVar(value=s.getbool("TransformSetup", "Insertpic"))
        self.v_ow = tk.BooleanVar(value=s.getbool("TransformSetup", "Overwrite"))
        self.v_play = tk.BooleanVar(value=s.getbool("TransformSetup", "Transplay"))
        self.v_copy = tk.BooleanVar(value=s.getbool("TransformSetup", "CopyFile"))
        self.v_del = tk.BooleanVar(value=s.getbool("Toolkit", "DeleteAfterCopy"))
        self.v_quirk = tk.BooleanVar(value=s.getbool("Toolkit", "VendorUpDownQuirk"))
        self.v_out = tk.StringVar(value=s.get("TransformSetup", "OUTPUTPATH"))
        self.v_drive = tk.StringVar()
        self._build()
        self._fill_sizes()
        self._on_fmt()
        self.refresh_drives()
        self.after(100, self._poll)

    # ------------------------------------------------------------------ construction
    def _build(self):
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)
        top = ttk.Frame(self)
        top.grid(row=0, column=0, sticky="nsew")
        top.columnconfigure(0, weight=1)
        top.rowconfigure(0, weight=1)
        cols = ("name", "info", "status")
        self.tree = ttk.Treeview(top, columns=cols, show="headings", height=6, selectmode="extended")
        for c, w in (("name", 300), ("info", 330), ("status", 150)):
            self.tree.heading(c, text=T("col_" + c))
            self.tree.column(c, width=w, anchor="w")
        sb = ttk.Scrollbar(top, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        btns = ttk.Frame(top)
        btns.grid(row=0, column=2, sticky="ns", padx=(8, 0))
        for txt, cmd in (("add_files", self.add_files), ("add_folder", self.add_folder), ("remove", self.remove_sel), ("clear", self.clear_all)):
            ttk.Button(btns, text=T(txt), command=cmd).pack(fill="x", pady=2)
        self.tree.bind("<Delete>", lambda e: self.remove_sel())
        # --- réglages
        mid = ttk.Frame(self)
        mid.grid(row=1, column=0, sticky="ew", pady=(8, 0))
        mid.columnconfigure(0, weight=1)
        mid.columnconfigure(1, weight=1)
        out = ttk.LabelFrame(mid, text=T("grp_output"), padding=8)
        out.grid(row=0, column=0, sticky="nsew", padx=(0, 4))
        out.columnconfigure(1, weight=1)
        r = 0
        ttk.Label(out, text=T("format")).grid(row=r, column=0, sticky="w")
        fr = ttk.Frame(out)
        fr.grid(row=r, column=1, sticky="w")
        for val in ("amv", "avi"):
            ttk.Radiobutton(fr, text=val.upper(), value=val, variable=self.v_fmt, command=self._on_fmt).pack(side="left", padx=(0, 10))
        r += 1
        ttk.Label(out, text=T("size")).grid(row=r, column=0, sticky="w")
        self.cb_size = ttk.Combobox(out, textvariable=self.v_size, state="readonly", width=14)
        self.cb_size.grid(row=r, column=1, sticky="w")
        self.cb_size.bind("<<ComboboxSelected>>", lambda e: self._on_size())
        r += 1
        cu = ttk.Frame(out)
        cu.grid(row=r, column=1, sticky="w")
        ttk.Checkbutton(cu, text=T("custom_size"), variable=self.v_custom, command=self._on_size).pack(side="left")
        self.sp_w = ttk.Spinbox(cu, from_=16, to=1280, increment=16, width=5, textvariable=self.v_w)
        self.sp_h = ttk.Spinbox(cu, from_=8, to=960, increment=8, width=5, textvariable=self.v_h)
        self.sp_w.pack(side="left", padx=(6, 2))
        ttk.Label(cu, text="×").pack(side="left")
        self.sp_h.pack(side="left", padx=(2, 0))
        Tooltip(self.sp_w, T("tip_custom"))
        r += 1
        ttk.Label(out, text=T("fps")).grid(row=r, column=0, sticky="w")
        ff = ttk.Frame(out)
        ff.grid(row=r, column=1, sticky="w")
        self.cb_fps = ttk.Combobox(ff, textvariable=self.v_fps, width=10)
        self.cb_fps.pack(side="left")
        self.lb_fps = ttk.Label(ff, text="", foreground="#666666")
        self.lb_fps.pack(side="left", padx=6)
        self.cb_fps.bind("<<ComboboxSelected>>", lambda e: self._update_fps_note())
        self.cb_fps.bind("<FocusOut>", lambda e: self._update_fps_note())
        r += 1
        ttk.Label(out, text=T("audio_rate")).grid(row=r, column=0, sticky="w")
        ar = ttk.Frame(out)
        ar.grid(row=r, column=1, sticky="w")
        self.rb_audio = []
        for val in AUDIO_RATES_AMV:
            rb = ttk.Radiobutton(ar, text="%d Hz" % val, value=val, variable=self.v_arate)
            rb.pack(side="left", padx=(0, 10))
            self.rb_audio.append(rb)
        r += 1
        ttk.Label(out, text=T("out_dir")).grid(row=r, column=0, sticky="w")
        od = ttk.Frame(out)
        od.grid(row=r, column=1, sticky="ew")
        od.columnconfigure(0, weight=1)
        ttk.Entry(od, textvariable=self.v_out).grid(row=0, column=0, sticky="ew")
        ttk.Button(od, text="…", width=3, command=self.pick_outdir).grid(row=0, column=1, padx=(4, 0))
        Tooltip(od, T("tip_outdir"))
        r += 1
        opts = ttk.Frame(out)
        opts.grid(row=r, column=0, columnspan=2, sticky="w", pady=(4, 0))
        ttk.Checkbutton(opts, text=T("overwrite"), variable=self.v_ow).grid(row=0, column=0, sticky="w", padx=(0, 12))
        ttk.Checkbutton(opts, text=T("play_after"), variable=self.v_play).grid(row=0, column=1, sticky="w")
        r += 1
        cp = ttk.Frame(out)
        cp.grid(row=r, column=0, columnspan=2, sticky="ew", pady=(4, 0))
        cp.columnconfigure(1, weight=1)
        ttk.Checkbutton(cp, text=T("copy_to"), variable=self.v_copy).grid(row=0, column=0, sticky="w")
        self.cb_drive = ttk.Combobox(cp, textvariable=self.v_drive, state="readonly")
        self.cb_drive.grid(row=0, column=1, sticky="ew", padx=4)
        ttk.Button(cp, text="↻", width=3, command=self.refresh_drives).grid(row=0, column=2)
        ttk.Checkbutton(cp, text=T("delete_after"), variable=self.v_del).grid(row=1, column=0, columnspan=3, sticky="w")
        # --- image et son
        img = ttk.LabelFrame(mid, text=T("grp_image"), padding=8)
        img.grid(row=0, column=1, sticky="nsew", padx=(4, 0))
        img.columnconfigure(1, weight=1)
        r = 0
        ttk.Label(img, text=T("orientation")).grid(row=r, column=0, sticky="w")
        self.cb_orient = ttk.Combobox(img, textvariable=self.v_orient, state="readonly", values=[T("orient_" + o) for o in ORIENTATIONS])
        self.cb_orient.grid(row=r, column=1, sticky="ew")
        r += 1
        ttk.Label(img, text=T("aspect")).grid(row=r, column=0, sticky="w")
        self.cb_aspect = ttk.Combobox(img, textvariable=self.v_aspect, state="readonly", values=[T("aspect_" + a) for a in ASPECT_MODES])
        self.cb_aspect.grid(row=r, column=1, sticky="ew")
        Tooltip(self.cb_aspect, T("tip_aspect"))
        r += 1
        ttk.Label(img, text=T("cut")).grid(row=r, column=0, sticky="w")
        cf = ttk.Frame(img)
        cf.grid(row=r, column=1, sticky="w")
        ttk.Label(cf, text=T("cut_start")).pack(side="left")
        ttk.Entry(cf, textvariable=self.v_start, width=9).pack(side="left", padx=(2, 8))
        ttk.Label(cf, text=T("cut_end")).pack(side="left")
        ttk.Entry(cf, textvariable=self.v_end, width=9).pack(side="left", padx=(2, 0))
        Tooltip(cf, T("tip_cut"))
        r += 1
        ttk.Label(img, text=T("audio_file")).grid(row=r, column=0, sticky="w")
        af = ttk.Frame(img)
        af.grid(row=r, column=1, sticky="ew")
        af.columnconfigure(0, weight=1)
        ttk.Entry(af, textvariable=self.v_afile).grid(row=0, column=0, sticky="ew")
        ttk.Button(af, text="…", width=3, command=self.pick_audio).grid(row=0, column=1, padx=(4, 0))
        r += 1
        ttk.Label(img, text=T("gain")).grid(row=r, column=0, sticky="w")
        gf = ttk.Frame(img)
        gf.grid(row=r, column=1, sticky="w")
        ttk.Spinbox(gf, from_=0.1, to=8.0, increment=0.1, width=6, textvariable=self.v_gain).pack(side="left")
        ttk.Label(gf, text="(ACOE)", foreground="#666666").pack(side="left", padx=6)
        r += 1
        ck = ttk.Frame(img)
        ck.grid(row=r, column=0, columnspan=2, sticky="w", pady=(4, 0))
        ttk.Checkbutton(ck, text=T("rgb565"), variable=self.v_565).grid(row=0, column=0, sticky="w", padx=(0, 12))
        ttk.Checkbutton(ck, text=T("insertwave"), variable=self.v_iw).grid(row=1, column=0, sticky="w", padx=(0, 12))
        ttk.Checkbutton(ck, text=T("insertpic"), variable=self.v_ip).grid(row=1, column=1, sticky="w")
        q = ttk.Checkbutton(ck, text=T("vendor_quirk"), variable=self.v_quirk)
        q.grid(row=2, column=0, columnspan=2, sticky="w")
        Tooltip(q, T("tip_quirk"))
        self._set_orient_aspect(s_orient=self.app.settings.get("Toolkit", "Orientation"), s_aspect=self.app.settings.get("Toolkit", "Aspect"))
        # --- barre d'actions
        act = ttk.Frame(self)
        act.grid(row=2, column=0, sticky="ew", pady=(8, 0))
        act.columnconfigure(2, weight=1)
        self.btn_start = ttk.Button(act, text=T("start"), style="Accent.TButton", command=self.start)
        self.btn_start.grid(row=0, column=0)
        self.btn_stop = ttk.Button(act, text=T("stop"), command=self.stop, state="disabled")
        self.btn_stop.grid(row=0, column=1, padx=6)
        self.lb_status = ttk.Label(act, text=T("ready"))
        self.lb_status.grid(row=0, column=2, sticky="w", padx=8)
        self.pb_file = ttk.Progressbar(self, maximum=1000)
        self.pb_file.grid(row=3, column=0, sticky="ew", pady=(6, 0))
        self.pb_all = ttk.Progressbar(self, maximum=1000)
        self.pb_all.grid(row=4, column=0, sticky="ew", pady=(3, 0))
        lg = ttk.Frame(self)
        lg.grid(row=5, column=0, sticky="nsew", pady=(6, 0))
        lg.columnconfigure(0, weight=1)
        self.rowconfigure(5, weight=1)
        self.log = tk.Text(lg, height=6, wrap="word", state="disabled", background=self.app.skin["field"])
        lsb = ttk.Scrollbar(lg, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=lsb.set)
        self.log.grid(row=0, column=0, sticky="nsew")
        lsb.grid(row=0, column=1, sticky="ns")

    # ------------------------------------------------------------------ réglages
    def _set_orient_aspect(self, s_orient, s_aspect):
        o = s_orient if s_orient in ORIENTATIONS else "normal"
        a = s_aspect if s_aspect in ASPECT_MODES else "stretch"
        self.v_orient.set(T("orient_" + o))
        self.v_aspect.set(T("aspect_" + a))

    def _orient_value(self):
        labels = [T("orient_" + o) for o in ORIENTATIONS]
        v = self.v_orient.get()
        return ORIENTATIONS[labels.index(v)] if v in labels else "normal"

    def _aspect_value(self):
        labels = [T("aspect_" + a) for a in ASPECT_MODES]
        v = self.v_aspect.get()
        return ASPECT_MODES[labels.index(v)] if v in labels else "stretch"

    def _sizes(self):
        return AMV_SIZES if self.v_fmt.get() == "amv" else AVI_SIZES

    def _fill_sizes(self):
        sizes = self._sizes()
        vals = ["%d x %d" % (w, h) for (w, h, _f) in sizes]
        self.cb_size.configure(values=vals)
        idx = min(int(self.app.settings.get("TransformSetup", "VWH") or DEFAULT_SIZE_INDEX), len(vals) - 1)
        cur = "%d x %d" % (self.v_w.get(), self.v_h.get())
        self.v_size.set(cur if cur in vals else vals[idx])
        self._on_size(init=True)

    def _on_fmt(self):
        amv = self.v_fmt.get() == "amv"
        for rb in self.rb_audio:
            rb.configure(state="normal" if amv else "disabled")
        self._fill_sizes()

    def _on_size(self, init=False):
        custom = self.v_custom.get()
        self.cb_size.configure(state="disabled" if custom else "readonly")
        for sp in (self.sp_w, self.sp_h):
            sp.configure(state="normal" if custom else "disabled")
        sizes = self._sizes()
        vals = ["%d x %d" % (w, h) for (w, h, _f) in sizes]
        if not custom and self.v_size.get() in vals:
            w, h, fps3 = sizes[vals.index(self.v_size.get())]
            self.v_w.set(w)
            self.v_h.set(h)
            self.cb_fps.configure(values=[str(x) for x in sorted(set(fps3))])
            level = {"low": 0, "mid": 1, "high": 2}.get(self.app.settings.get("TransformSetup", "VFBS"), 2)
            if not init or not self.v_fps.get():
                self.v_fps.set(str(fps3[level]))
        elif custom:
            self.cb_fps.configure(values=["14", "16", "20", "22", "25", "30"])
            if not self.v_fps.get():
                self.v_fps.set("25")
        self._update_fps_note()

    def _update_fps_note(self):
        try:
            f = int(float(self.v_fps.get()))
        except ValueError:
            self.lb_fps.configure(text="")
            return
        if self.v_fmt.get() == "avi":
            spb = avi_samples_per_block(f)
            self.lb_fps.configure(text=T("fps_avi_note") % (AVI_AUDIO_RATE / spb))
        else:
            self.lb_fps.configure(text=T("fps_unit"))

    # ------------------------------------------------------------------ fichiers
    def pick_outdir(self):
        d = filedialog.askdirectory(title=T("out_dir"))
        if d:
            self.v_out.set(d)

    def pick_audio(self):
        f = filedialog.askopenfilename(title=T("audio_file"), filetypes=[(T("ft_audio"), "*.mp3 *.wav *.wma *.ogg *.m4a *.aac *.flac"), (T("ft_all"), "*.*")])
        if f:
            self.v_afile.set(f)

    def add_files(self):
        pats = " ".join("*" + e for e in VIDEO_EXTENSIONS)
        fl = filedialog.askopenfilenames(title=T("add_files"), filetypes=[(T("ft_video"), pats), (T("ft_all"), "*.*")])
        self.add_paths(fl)

    def add_folder(self):
        d = filedialog.askdirectory(title=T("add_folder"))
        if d:
            paths = [os.path.join(d, f) for f in sorted(os.listdir(d)) if f.lower().endswith(VIDEO_EXTENSIONS)]
            self.add_paths(paths)

    def add_paths(self, paths):
        for p in paths:
            p = os.path.abspath(p)
            if any(f["path"] == p for f in self.files):
                continue
            try:
                if p.lower().endswith(".amv"):
                    m = AmvFile(p)
                    info = "AMV %dx%d %.1f i/s  %s" % (m.width, m.height, m.fps, fmt_time(m.duration))
                else:
                    mi = probe(p)
                    info = mi.describe()
                    if not mi.has_video:
                        raise ToolError(T("no_video"))
                status = T("st_ready")
            except Exception as e:
                info, status = str(e)[:90], T("st_error")
            self.files.append({"path": p, "info": info, "status": status})
        self._refresh_tree()

    def remove_sel(self):
        sel = set(self.tree.selection())
        self.files = [f for i, f in enumerate(self.files) if str(i) not in sel]
        self._refresh_tree()

    def clear_all(self):
        if self.worker and self.worker.is_alive():
            return
        self.files = []
        self._refresh_tree()

    def _refresh_tree(self):
        self.tree.delete(*self.tree.get_children())
        for i, f in enumerate(self.files):
            self.tree.insert("", "end", iid=str(i), values=(os.path.basename(f["path"]), f["info"], f["status"]))

    def refresh_drives(self):
        self.drives = list_drives()
        vals = [_first_drive_text(d) for d in self.drives]
        self.cb_drive.configure(values=vals)
        if vals:
            if self.v_drive.get() not in vals:
                self.v_drive.set(vals[0])
        else:
            self.v_drive.set(T("no_device"))

    # ------------------------------------------------------------------ exécution
    def build_options(self):
        try:
            fps = int(round(float(self.v_fps.get())))
        except ValueError:
            raise ValueError(T("err_fps"))
        o = ConvertOptions(
            fmt=self.v_fmt.get(), width=int(self.v_w.get()), height=int(self.v_h.get()), fps=fps, audio_rate=int(self.v_arate.get()),
            orientation=self._orient_value(), aspect=self._aspect_value(), start=parse_time(self.v_start.get()), end=parse_time(self.v_end.get()),
            audio_file=self.v_afile.get().strip(), gain=float(self.v_gain.get()), rgb565=self.v_565.get(), insertwave=self.v_iw.get(),
            insertpic=self.v_ip.get(), overwrite=self.v_ow.get(), outdir=self.v_out.get().strip(), vendor_updown_quirk=self.v_quirk.get())
        validate_options(o)
        return o

    def save_settings(self):
        s = self.app.settings
        s.set("Toolkit", "Format", self.v_fmt.get())
        s.set("Toolkit", "Width", str(self.v_w.get()))
        s.set("Toolkit", "Height", str(self.v_h.get()))
        s.set("Toolkit", "CustomSize", str(self.v_custom.get()).upper())
        s.set("Toolkit", "AudioRate", str(self.v_arate.get()))
        s.set("Toolkit", "Orientation", self._orient_value())
        s.set("Toolkit", "Aspect", self._aspect_value())
        s.set("Toolkit", "Gain", "%.2f" % float(self.v_gain.get()))
        s.set("Toolkit", "RGB565", str(self.v_565.get()).upper())
        s.set("Toolkit", "DeleteAfterCopy", str(self.v_del.get()).upper())
        s.set("Toolkit", "VendorUpDownQuirk", str(self.v_quirk.get()).upper())
        for key, var in (("Insertwave", self.v_iw), ("Insertpic", self.v_ip), ("Overwrite", self.v_ow), ("Transplay", self.v_play), ("CopyFile", self.v_copy)):
            s.set("TransformSetup", key, str(var.get()).upper())
        s.set("TransformSetup", "OUTPUTPATH", self.v_out.get().strip())
        sizes = self._sizes()
        vals = ["%d x %d" % (w, h) for (w, h, _f) in sizes]
        if self.v_size.get() in vals:
            s.set("TransformSetup", "VWH", str(vals.index(self.v_size.get())))
        try:
            f = int(float(self.v_fps.get()))
            fps3 = sizes[vals.index(self.v_size.get())][2] if self.v_size.get() in vals else None
            if fps3:
                s.set("TransformSetup", "VFBS", ("low", "mid", "high")[min(range(3), key=lambda i: abs(fps3[i] - f))])
        except ValueError:
            pass
        s.save()

    def logmsg(self, text):
        self.log.configure(state="normal")
        self.log.insert("end", text + "\n")
        self.log.see("end")
        self.log.configure(state="disabled")

    def start(self):
        if self.worker and self.worker.is_alive():
            return
        todo = [f for f in self.files if f["status"] != T("st_error")]
        if not todo:
            messagebox.showinfo(APP_NAME, T("nothing_to_do"))
            return
        try:
            o = self.build_options()
        except Exception as e:
            messagebox.showerror(APP_NAME, str(e))
            return
        if not find_tool("ffmpeg") or not find_tool("ffprobe"):
            messagebox.showerror(APP_NAME, T("no_ffmpeg"))
            return
        self.save_settings()
        drive = None
        if self.v_copy.get() and self.drives:
            txt = self.v_drive.get()
            for d in self.drives:
                if _first_drive_text(d) == txt:
                    drive = d["path"]
        self.cancel.clear()
        self.btn_start.configure(state="disabled")
        self.btn_stop.configure(state="normal")
        for f in todo:
            f["status"] = T("st_waiting")
        self._refresh_tree()
        self.worker = threading.Thread(target=self._work, args=(todo, o, drive, self.v_del.get()), daemon=True)
        self.worker.start()

    def stop(self):
        self.cancel.set()
        self.lb_status.configure(text=T("stopping"))

    def _work(self, jobs, o, drive, delete_after):
        total = len(jobs)
        outs = []
        for n, f in enumerate(jobs):
            if self.cancel.is_set():
                break
            dst = default_output_path(f["path"], o)
            self.q.put(("status", f, T("st_converting")))
            self.q.put(("log", T("log_start") % (os.path.basename(f["path"]), dst)))
            if os.path.abspath(dst) == os.path.abspath(f["path"]):
                self.q.put(("status", f, T("st_error")))
                self.q.put(("log", T("err_same_file")))
                continue
            if os.path.exists(dst) and not o.overwrite:
                ev, box = threading.Event(), []
                self.q.put(("ask", dst, ev, box))
                ev.wait()
                if not (box and box[0]):
                    self.q.put(("status", f, T("st_skipped")))
                    continue
            try:
                r = convert_file(f["path"], dst, ConvertOptions(**{**o.__dict__, "overwrite": True}),
                                 progress=lambda fr, t, n=n: self.q.put(("prog", fr, (n + fr) / total, t)),
                                 cancel=self.cancel, log=lambda m: self.q.put(("log", m)))
                self.q.put(("status", f, T("st_done")))
                self.q.put(("log", T("log_done") % (r["frames"], r["seconds"], fmt_size(r["bytes"]), r["elapsed"])))
                outs.append(dst)
                if drive:
                    try:
                        copy_to_device(dst, drive, delete_after)
                        self.q.put(("log", T("log_copied") % drive))
                    except Exception as e:
                        self.q.put(("log", T("err_copy") % e))
            except Cancelled:
                self.q.put(("status", f, T("st_cancelled")))
                break
            except Exception as e:
                self.q.put(("status", f, T("st_error")))
                self.q.put(("log", T("err_convert") % e))
        self.q.put(("finished", outs))

    def _poll(self):
        try:
            while True:
                msg = self.q.get_nowait()
                k = msg[0]
                if k == "log":
                    self.logmsg(msg[1])
                elif k == "status":
                    msg[1]["status"] = msg[2]
                    self._refresh_tree()
                elif k == "prog":
                    self.pb_file["value"] = msg[1] * 1000
                    self.pb_all["value"] = msg[2] * 1000
                    self.lb_status.configure(text=msg[3])
                elif k == "ask":
                    ans = messagebox.askyesno(APP_NAME, T("ask_overwrite") % os.path.basename(msg[1]))
                    msg[3].append(ans)
                    msg[2].set()
                elif k == "finished":
                    self.btn_start.configure(state="normal")
                    self.btn_stop.configure(state="disabled")
                    self.lb_status.configure(text=T("finished"))
                    self.pb_file["value"] = 0
                    if msg[1]:
                        self.pb_all["value"] = 1000
                        if self.v_play.get() and not self.cancel.is_set():
                            self.app.open_in_player(msg[1][-1])
        except queue.Empty:
            pass
        self.after(100, self._poll)



class PlayerTab(ttk.Frame):
    """Onglet « Lecteur » : équivalent d'AMVPlayer (lecture, pause, précédent/suivant, avance/retour, répétition, adaptation, zoom, plein écran, propriétés)."""

    def __init__(self, master, app):
        super().__init__(master, padding=6)
        self.app = app
        s = app.settings
        self.m = None
        self.path = ""
        self.audio = None
        self.playing = False
        self.cur = 0
        self.t0 = 0.0
        self.base_idx = 0
        self.zoom = 1.0
        self.cache = {}
        self.photo = None
        self.v_repeat = tk.BooleanVar(value=s.getbool("PlayerSetup", "repeat"))
        self.v_adjust = tk.BooleanVar(value=s.getbool("PlayerSetup", "adjust"))
        self._seeking = False
        self._build()

    def _build(self):
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)
        self.canvas = tk.Canvas(self, background="#000000", highlightthickness=0, width=480, height=320)
        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.canvas.bind("<Configure>", lambda e: self._redraw())
        self.canvas.bind("<Button-1>", lambda e: self.toggle())
        self.canvas.bind("<Double-Button-1>", lambda e: self.fullscreen())
        bar = ttk.Frame(self)
        bar.grid(row=1, column=0, sticky="ew", pady=(6, 0))
        bar.columnconfigure(6, weight=1)
        self.btn = {}
        specs = (("open", self.ask_open), ("prev", lambda: self.step_file(-1)), ("backward", lambda: self.seek_rel(-5)), ("play", self.toggle),
                 ("forward", lambda: self.seek_rel(5)), ("next", lambda: self.step_file(1)))
        for i, (k, cmd) in enumerate(specs):
            b = ttk.Button(bar, text=T("pl_" + k), command=cmd, width=10 if k in ("open", "play") else 9)
            b.grid(row=0, column=i, padx=2)
            self.btn[k] = b
        self.scale = ttk.Scale(bar, from_=0, to=1, orient="horizontal", command=self._on_scale)
        self.scale.grid(row=0, column=6, sticky="ew", padx=8)
        self.scale.bind("<ButtonPress-1>", lambda e: setattr(self, "_seeking", True))
        self.scale.bind("<ButtonRelease-1>", self._scale_release)
        self.lb_time = ttk.Label(bar, text="00:00 / 00:00", width=14)
        self.lb_time.grid(row=0, column=7, padx=4)
        bar2 = ttk.Frame(self)
        bar2.grid(row=2, column=0, sticky="ew", pady=(4, 0))
        ttk.Checkbutton(bar2, text=T("pl_repeat"), variable=self.v_repeat).pack(side="left", padx=4)
        ttk.Checkbutton(bar2, text=T("pl_adjust"), variable=self.v_adjust, command=self._redraw).pack(side="left", padx=4)
        for k, f in (("amplify", 1.25), ("reduce", 0.8), ("equal", None)):
            ttk.Button(bar2, text=T("pl_" + k), width=9, command=lambda f=f: self.set_zoom(f)).pack(side="left", padx=2)
        ttk.Button(bar2, text=T("pl_property"), command=self.show_properties).pack(side="left", padx=(10, 2))
        ttk.Button(bar2, text=T("pl_snapshot"), command=self.snapshot).pack(side="left", padx=2)
        ttk.Button(bar2, text=T("pl_fullscreen"), command=self.fullscreen).pack(side="left", padx=2)
        self.lb_info = ttk.Label(self, text=T("pl_noaudio_hint"), foreground="#555555")
        self.lb_info.grid(row=3, column=0, sticky="w", padx=4, pady=(4, 0))

    # ------------------------------------------------------------------ fichier
    def ask_open(self):
        f = filedialog.askopenfilename(title=T("pl_open"), filetypes=[("AMV / AVI", "*.amv *.avi"), (T("ft_all"), "*.*")])
        if f:
            self.open(f)

    def open(self, path):
        self.stop()
        try:
            m = open_media(path)
            if m.nframes == 0:
                raise MediaFileError(T("pl_empty"))
        except Exception as e:
            messagebox.showerror(APP_NAME, "%s\n%s" % (path, e))
            return False
        if self.audio:
            self.audio.cleanup()
        self.m, self.path = m, path
        self.audio = AudioPlayer(m)
        self.cache = {}
        self.cur = 0
        self.scale.configure(to=max(1, m.nframes - 1))
        self.show(0)
        self.lb_info.configure(text=("%s  %dx%d  %.2f i/s" % (os.path.basename(path), m.width, m.height, m.fps)) + ("" if self.audio.available() else "  — " + T("pl_noaudio")))
        self.app.title("%s — %s" % (APP_NAME, os.path.basename(path)))
        return True

    def step_file(self, d):
        if not self.path:
            return
        folder = os.path.dirname(self.path)
        names = sorted(f for f in os.listdir(folder) if f.lower().endswith((".amv", ".avi")))
        cur = os.path.basename(self.path)
        if cur not in names:
            return
        j = (names.index(cur) + d) % len(names)
        was = self.playing
        if self.open(os.path.join(folder, names[j])) and was:
            self.play()

    # ------------------------------------------------------------------ affichage
    def _frame(self, i):
        if i in self.cache:
            return self.cache[i]
        rgb = self.m.frame_rgb(i)
        if len(self.cache) > 48:
            self.cache.pop(next(iter(self.cache)))
        self.cache[i] = rgb
        return rgb

    def show(self, i):
        if not self.m:
            return
        i = max(0, min(self.m.nframes - 1, i))
        self.cur = i
        self._draw(self._frame(i))
        t = i / self.m.fps
        self.lb_time.configure(text="%s / %s" % (fmt_time(t), fmt_time(self.m.duration)))
        if not self._seeking:
            self.scale.configure(command=None)
            self.scale.set(i)
            self.scale.configure(command=self._on_scale)

    def _target_size(self, w, h):
        cw, ch = max(self.canvas.winfo_width(), 16), max(self.canvas.winfo_height(), 16)
        if self.v_adjust.get():
            sc = min(cw / w, ch / h)
        else:
            sc = self.zoom
        return max(1, int(w * sc)), max(1, int(h * sc))

    def _draw(self, rgb):
        h, w, _ = rgb.shape
        tw, th = self._target_size(w, h)
        if (tw, th) != (w, h):
            if tw % w == 0 and th % h == 0:
                rgb = np.repeat(np.repeat(rgb, th // h, axis=0), tw // w, axis=1)
            else:
                ys = (np.arange(th) * h) // th
                xs = (np.arange(tw) * w) // tw
                rgb = rgb[ys][:, xs]
        ppm = b"P6 %d %d 255\n" % (rgb.shape[1], rgb.shape[0]) + np.ascontiguousarray(rgb).tobytes()
        self.photo = tk.PhotoImage(data=ppm)
        self.canvas.delete("all")
        cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
        self.canvas.create_image(cw // 2, ch // 2, image=self.photo, anchor="center")

    def _redraw(self):
        if self.m:
            self._draw(self._frame(self.cur))

    def set_zoom(self, f):
        self.zoom = 1.0 if f is None else max(0.25, min(8.0, self.zoom * f))
        self.v_adjust.set(False)
        self._redraw()

    # ------------------------------------------------------------------ lecture
    def toggle(self):
        if not self.m:
            return
        self.pause() if self.playing else self.play()

    def play(self):
        if not self.m or self.playing:
            return
        if self.cur >= self.m.nframes - 1:
            self.cur = 0
        self.playing = True
        self.base_idx = self.cur
        self.t0 = time.perf_counter()
        self.btn["play"].configure(text=T("pl_pause"))
        if self.audio:
            self.audio.start(self.cur)
        self.after(1, self._tick)

    def pause(self):
        self.playing = False
        self.btn["play"].configure(text=T("pl_play"))
        if self.audio:
            self.audio.stop()

    def stop(self):
        self.pause()
        if self.m:
            self.show(0)

    def _tick(self):
        if not self.playing or not self.m:
            return
        idx = self.base_idx + int((time.perf_counter() - self.t0) * self.m.fps)
        if idx >= self.m.nframes:
            if self.v_repeat.get():
                self.cur = 0
                self.playing = False
                self.play()
                return
            self.pause()
            self.show(self.m.nframes - 1)
            return
        if idx != self.cur:
            self.show(idx)
        self.after(4, self._tick)

    def seek_rel(self, sec):
        if self.m:
            self.seek(self.cur + int(sec * self.m.fps))

    def seek(self, idx):
        if not self.m:
            return
        idx = max(0, min(self.m.nframes - 1, idx))
        was = self.playing
        if was:
            self.pause()
        self.show(idx)
        if was:
            self.play()

    def _on_scale(self, v):
        if self._seeking and self.m:
            self.show(int(float(v)))

    def _scale_release(self, _e):
        self._seeking = False
        if self.m:
            self.seek(int(float(self.scale.get())))

    # ------------------------------------------------------------------ divers
    def fullscreen(self):
        on = not bool(self.app.attributes("-fullscreen"))
        self.app.attributes("-fullscreen", on)
        self.after(150, self._redraw)

    def show_properties(self):
        if not self.m:
            return
        win = tk.Toplevel(self)
        win.title(T("pl_property"))
        win.transient(self.app)
        txt = "\n".join("%-28s %s" % (k + " :", v) for k, v in file_properties(self.m).items())
        tk.Label(win, text=os.path.basename(self.path), font=("TkDefaultFont", 10, "bold")).pack(padx=12, pady=(10, 4), anchor="w")
        tk.Label(win, text=txt, justify="left", font=("TkFixedFont", 9)).pack(padx=12, pady=4, anchor="w")
        ttk.Button(win, text="OK", command=win.destroy).pack(pady=8)

    def snapshot(self):
        if not self.m:
            return
        d = self.app.settings.get("PlayerSetup", "bmpdir")
        folder = d if d and os.path.isdir(d) else os.path.dirname(self.path)
        dst = os.path.join(folder, "%s_%05d.png" % (os.path.splitext(os.path.basename(self.path))[0], self.cur))
        try:
            extract_frame(self.m, self.cur, dst)
            self.lb_info.configure(text=T("pl_saved") % os.path.basename(dst))
        except OSError as e:
            messagebox.showerror(APP_NAME, str(e))

    def on_key(self, e):
        k = e.keysym
        if k == "space":
            self.toggle()
        elif k == "Left":
            self.seek_rel(-5)
        elif k == "Right":
            self.seek_rel(5)
        elif k == "F11":
            self.fullscreen()
        elif k == "Escape" and self.app.attributes("-fullscreen"):
            self.fullscreen()

    def save_settings(self):
        s = self.app.settings
        s.set("PlayerSetup", "repeat", str(self.v_repeat.get()).upper())
        s.set("PlayerSetup", "adjust", str(self.v_adjust.get()).upper())

    def shutdown(self):
        self.playing = False
        if self.audio:
            self.audio.cleanup()



class ToolsTab(ttk.Frame):
    """Onglet « Outils » : propriétés, vérification, export vers MP4, extraction audio/image d'un fichier AMV/AVI."""

    def __init__(self, master, app):
        super().__init__(master, padding=8)
        self.app = app
        self.q = queue.Queue()
        self.v_path = tk.StringVar()
        self.v_frame = tk.IntVar(value=0)
        self.columnconfigure(0, weight=1)
        self.rowconfigure(2, weight=1)
        top = ttk.Frame(self)
        top.grid(row=0, column=0, sticky="ew")
        top.columnconfigure(0, weight=1)
        ttk.Entry(top, textvariable=self.v_path).grid(row=0, column=0, sticky="ew")
        ttk.Button(top, text=T("browse"), command=self.browse).grid(row=0, column=1, padx=(6, 0))
        bar = ttk.Frame(self)
        bar.grid(row=1, column=0, sticky="ew", pady=8)
        for key, cmd in (("tl_props", self.do_props), ("tl_verify", self.do_verify), ("tl_export", self.do_export), ("tl_wav", self.do_wav),
                         ("tl_player", self.do_player)):
            ttk.Button(bar, text=T(key), command=cmd).pack(side="left", padx=(0, 6))
        ttk.Label(bar, text=T("tl_frame")).pack(side="left", padx=(12, 2))
        ttk.Spinbox(bar, from_=0, to=999999, width=7, textvariable=self.v_frame).pack(side="left")
        ttk.Button(bar, text=T("tl_saveframe"), command=self.do_frame).pack(side="left", padx=6)
        self.out = tk.Text(self, wrap="word", height=14, state="disabled", font=("TkFixedFont", 9), background=app.skin["field"])
        self.out.grid(row=2, column=0, sticky="nsew")
        self.pb = ttk.Progressbar(self, maximum=1000)
        self.pb.grid(row=3, column=0, sticky="ew", pady=(8, 0))
        self.after(120, self._poll)

    def say(self, text, clear=False):
        self.out.configure(state="normal")
        if clear:
            self.out.delete("1.0", "end")
        self.out.insert("end", text + "\n")
        self.out.see("end")
        self.out.configure(state="disabled")

    def browse(self):
        f = filedialog.askopenfilename(filetypes=[("AMV / AVI", "*.amv *.avi"), (T("ft_all"), "*.*")])
        if f:
            self.v_path.set(f)

    def _media(self):
        p = self.v_path.get().strip()
        if not p or not os.path.isfile(p):
            messagebox.showinfo(APP_NAME, T("tl_choose"))
            return None
        try:
            return open_media(p)
        except Exception as e:
            messagebox.showerror(APP_NAME, str(e))
            return None

    def do_props(self):
        m = self._media()
        if m:
            self.say("\n".join("%-30s %s" % (k + " :", v) for k, v in file_properties(m).items()), clear=True)

    def do_verify(self):
        p = self.v_path.get().strip()
        if not os.path.isfile(p):
            messagebox.showinfo(APP_NAME, T("tl_choose"))
            return
        ok, msgs = verify_file(p)
        self.say("\n".join(msgs), clear=True)

    def do_export(self):
        m = self._media()
        if not m:
            return
        dst = filedialog.asksaveasfilename(defaultextension=".mp4", filetypes=[("MP4", "*.mp4"), ("AVI", "*.avi"), ("MKV", "*.mkv")],
                                           initialfile=os.path.splitext(os.path.basename(self.v_path.get()))[0] + ".mp4")
        if not dst:
            return
        if not find_tool("ffmpeg"):
            messagebox.showerror(APP_NAME, T("no_ffmpeg"))
            return
        src = self.v_path.get()
        self.say(T("tl_exporting") % dst, clear=True)

        def run():
            try:
                r = export_to_video(src, dst, progress=lambda f, t: self.q.put(("p", f)))
                self.q.put(("say", T("tl_exported") % (r["frames"], fmt_size(r["bytes"]))))
            except Exception as e:
                self.q.put(("say", T("err_convert") % e))
            self.q.put(("p", 0))
        threading.Thread(target=run, daemon=True).start()

    def do_wav(self):
        m = self._media()
        if not m:
            return
        dst = filedialog.asksaveasfilename(defaultextension=".wav", filetypes=[("WAV", "*.wav")])
        if dst:
            write_wav(dst, m.audio_pcm(), m.audio_rate)
            self.say(T("tl_saved") % dst)

    def do_frame(self):
        m = self._media()
        if not m:
            return
        i = max(0, min(m.nframes - 1, int(self.v_frame.get())))
        dst = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("PNG", "*.png"), ("BMP", "*.bmp")])
        if dst:
            extract_frame(m, i, dst)
            self.say(T("tl_saved") % dst)

    def do_player(self):
        p = self.v_path.get().strip()
        if os.path.isfile(p):
            self.app.open_in_player(p)

    def _poll(self):
        try:
            while True:
                k, v = self.q.get_nowait()
                if k == "say":
                    self.say(v)
                else:
                    self.pb["value"] = v * 1000
        except queue.Empty:
            pass
        self.after(120, self._poll)


class MediaGetTab(ttk.Frame):
    """Onglet « MediaGet » : liste d'URL à télécharger (équivalent simplifié de net.dll / grabcom.ocx)."""

    def __init__(self, master, app):
        super().__init__(master, padding=8)
        self.app = app
        self.items = []
        self.q = queue.Queue()
        self.v_url = tk.StringVar()
        d = app.settings.get("TransformSetup", "OUTPUTPATH")
        self.v_dir = tk.StringVar(value=d if d and os.path.isdir(d) else os.path.join(os.path.expanduser("~"), "Downloads"))
        self.columnconfigure(0, weight=1)
        self.rowconfigure(2, weight=1)
        top = ttk.Frame(self)
        top.grid(row=0, column=0, sticky="ew")
        top.columnconfigure(0, weight=1)
        e = ttk.Entry(top, textvariable=self.v_url)
        e.grid(row=0, column=0, sticky="ew")
        e.bind("<Return>", lambda ev: self.add_url())
        ttk.Button(top, text=T("mg_add"), command=self.add_url).grid(row=0, column=1, padx=4)
        ttk.Button(top, text=T("mg_scan"), command=self.scan_page).grid(row=0, column=2)
        d2 = ttk.Frame(self)
        d2.grid(row=1, column=0, sticky="ew", pady=6)
        d2.columnconfigure(1, weight=1)
        ttk.Label(d2, text=T("mg_dir")).grid(row=0, column=0)
        ttk.Entry(d2, textvariable=self.v_dir).grid(row=0, column=1, sticky="ew", padx=4)
        ttk.Button(d2, text="…", width=3, command=self.pick_dir).grid(row=0, column=2)
        cols = ("n", "name", "size", "prog", "speed", "state")
        self.tree = ttk.Treeview(self, columns=cols, show="headings", selectmode="extended", height=8)
        for c, w in (("n", 40), ("name", 300), ("size", 90), ("prog", 80), ("speed", 90), ("state", 110)):
            self.tree.heading(c, text=T("mg_" + c))
            self.tree.column(c, width=w, anchor="w")
        self.tree.grid(row=2, column=0, sticky="nsew")
        bar = ttk.Frame(self)
        bar.grid(row=3, column=0, sticky="ew", pady=6)
        for key, cmd in (("mg_download", self.start_sel), ("mg_stop", self.stop_sel), ("mg_delete", self.delete_sel), ("mg_sendconv", self.send_to_converter)):
            ttk.Button(bar, text=T(key), command=cmd).pack(side="left", padx=(0, 6))
        self.lb = ttk.Label(self, text="")
        self.lb.grid(row=4, column=0, sticky="w")
        self.after(300, self._poll)

    def pick_dir(self):
        d = filedialog.askdirectory()
        if d:
            self.v_dir.set(d)

    def add_url(self, url=None):
        url = (url or self.v_url.get()).strip()
        if not url:
            return
        if not re.match(r"^https?://", url, re.I):
            messagebox.showerror(APP_NAME, T("mg_badurl"))
            return
        self.items.append(DownloadItem(url, self.v_dir.get()))
        self.v_url.set("")
        self._refresh()

    def scan_page(self):
        url = self.v_url.get().strip()
        if not re.match(r"^https?://", url, re.I):
            messagebox.showerror(APP_NAME, T("mg_badurl"))
            return
        self.lb.configure(text=T("mg_scanning"))

        def run():
            try:
                links = find_media_links(url)
                self.q.put(("links", links))
            except Exception as e:
                self.q.put(("err", str(e)))
        threading.Thread(target=run, daemon=True).start()

    def _sel_items(self):
        sel = [int(i) for i in self.tree.selection()]
        return [self.items[i] for i in sel] if sel else list(self.items)

    def start_sel(self):
        for it in self._sel_items():
            if it.state in ("ready", "stopped", "error"):
                it.done = 0
                it.path = os.path.join(self.v_dir.get(), it.name)
                os.makedirs(self.v_dir.get(), exist_ok=True)
                threading.Thread(target=download, args=(it, lambda i: self.q.put(("prog", i))), daemon=True).start()

    def stop_sel(self):
        for it in self._sel_items():
            it.cancel.set()

    def delete_sel(self):
        sel = {int(i) for i in self.tree.selection()}
        for it in [self.items[i] for i in sel]:
            it.cancel.set()
        self.items = [it for i, it in enumerate(self.items) if i not in sel]
        self._refresh()

    def send_to_converter(self):
        ok = [it.path for it in self._sel_items() if it.state == "success" and os.path.isfile(it.path)]
        if ok:
            self.app.convert_tab.add_paths(ok)
            self.app.nb.select(self.app.convert_tab)

    def _refresh(self):
        self.tree.delete(*self.tree.get_children())
        for i, it in enumerate(self.items):
            pct = ("%d %%" % (100 * it.done // it.size)) if it.size else (fmt_size(it.done) if it.done else "")
            state = T("mg_state_" + it.state) + ((": " + it.error[:40]) if it.error else "")
            self.tree.insert("", "end", iid=str(i), values=(i + 1, it.name, fmt_size(it.size) if it.size else "?", pct, fmt_size(it.speed) + "/s" if it.speed else "", state))

    def _poll(self):
        dirty = False
        try:
            while True:
                m = self.q.get_nowait()
                if m[0] == "links":
                    for u in m[1]:
                        self.add_url(u)
                    self.lb.configure(text=T("mg_found") % len(m[1]))
                elif m[0] == "err":
                    self.lb.configure(text=m[1][:120])
                else:
                    dirty = True
        except queue.Empty:
            pass
        if dirty:
            self._refresh()
        self.after(300, self._poll)

    def shutdown(self):
        for it in self.items:
            it.cancel.set()


class AboutTab(ttk.Frame):
    def __init__(self, master, app):
        super().__init__(master, padding=12)
        self.app = app
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)
        self.txt = tk.Text(self, wrap="word", state="disabled", background=app.skin["field"], height=18)
        self.txt.grid(row=0, column=0, sticky="nsew")
        bar = ttk.Frame(self)
        bar.grid(row=1, column=0, sticky="ew", pady=8)
        ttk.Button(bar, text=T("ab_pick_ffmpeg"), command=self.pick_ffmpeg).pack(side="left")
        ttk.Button(bar, text=T("ab_refresh"), command=self.refresh).pack(side="left", padx=6)
        self.refresh()

    def refresh(self):
        ff = find_tool("ffmpeg")
        ver = ""
        if ff:
            try:
                ver = subprocess.run([ff, "-version"], capture_output=True, text=True, **_NO_WINDOW).stdout.splitlines()[0]
            except Exception:
                ver = ""
        text = T("about_text") % (APP_NAME, APP_VERSION, ORIGINAL_VERSION, ff or T("ab_missing"), ver, find_tool("ffprobe") or T("ab_missing"),
                                  AudioPlayer.detect() or T("ab_noaudio"), self.app.settings.path)
        self.txt.configure(state="normal")
        self.txt.delete("1.0", "end")
        self.txt.insert("end", text)
        self.txt.configure(state="disabled")

    def pick_ffmpeg(self):
        global FFMPEG_DIR_OVERRIDE
        d = filedialog.askdirectory(title=T("ab_pick_ffmpeg"))
        if d:
            FFMPEG_DIR_OVERRIDE = d
            self.app.settings.set("Toolkit", "FFmpegDir", d)
            self.app.settings.save()
            self.refresh()


class App(tk.Tk if TK_OK else object):
    def __init__(self, files=None):
        super().__init__()
        global FFMPEG_DIR_OVERRIDE
        self.settings = Settings()
        set_lang(self.settings.get("Toolkit", "Language"))
        d = self.settings.get("Toolkit", "FFmpegDir")
        if d and os.path.isdir(d):
            FFMPEG_DIR_OVERRIDE = d
        self.skin = apply_skin(self, "ocean" if self.settings.get("PlayerSetup", "Skin") == "1" else "classic")
        self.title("%s %s" % (APP_NAME, APP_VERSION))
        self.geometry("1000x760")
        self.minsize(900, 640)
        self.nb = ttk.Notebook(self)
        self.nb.pack(fill="both", expand=True, padx=6, pady=6)
        self.convert_tab = ConvertTab(self.nb, self)
        self.player_tab = PlayerTab(self.nb, self)
        self.tools_tab = ToolsTab(self.nb, self)
        self.mg_tab = MediaGetTab(self.nb, self)
        self.about_tab = AboutTab(self.nb, self)
        for tab, key in ((self.convert_tab, "tab_convert"), (self.player_tab, "tab_player"), (self.tools_tab, "tab_tools"),
                         (self.mg_tab, "tab_mediaget"), (self.about_tab, "tab_about")):
            self.nb.add(tab, text=T(key))
        self._menu()
        self.bind("<Key>", self._on_key)
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        if files:
            self.convert_tab.add_paths([f for f in files if os.path.isfile(f)])

    def _menu(self):
        mb = tk.Menu(self)
        fm = tk.Menu(mb, tearoff=0)
        fm.add_command(label=T("add_files"), command=self.convert_tab.add_files)
        fm.add_command(label=T("pl_open"), command=lambda: (self.nb.select(self.player_tab), self.player_tab.ask_open()))
        fm.add_separator()
        fm.add_command(label=T("quit"), command=self.on_close)
        mb.add_cascade(label=T("menu_file"), menu=fm)
        vm = tk.Menu(mb, tearoff=0)
        for code, name in (("fr", "Français"), ("en", "English")):
            vm.add_command(label=name, command=lambda c=code: self.set_language(c))
        vm.add_separator()
        vm.add_command(label="Skin : Classic", command=lambda: self.set_skin("0"))
        vm.add_command(label="Skin : Ocean", command=lambda: self.set_skin("1"))
        mb.add_cascade(label=T("menu_view"), menu=vm)
        hm = tk.Menu(mb, tearoff=0)
        hm.add_command(label=T("tab_about"), command=lambda: self.nb.select(self.about_tab))
        mb.add_cascade(label=T("menu_help"), menu=hm)
        self.configure(menu=mb)

    def set_language(self, code):
        self.settings.set("Toolkit", "Language", code)
        self.settings.save()
        messagebox.showinfo(APP_NAME, T("restart_needed"))

    def set_skin(self, v):
        self.settings.set("PlayerSetup", "Skin", v)
        self.settings.set("TransformSetup", "Skin", v)
        self.skin = apply_skin(self, "ocean" if v == "1" else "classic")
        self.settings.save()

    def _on_key(self, e):
        if self.nb.select() == str(self.player_tab) and not isinstance(self.focus_get(), (tk.Entry, ttk.Entry, ttk.Spinbox, ttk.Combobox)):
            self.player_tab.on_key(e)

    def open_in_player(self, path):
        self.nb.select(self.player_tab)
        self.update_idletasks()
        if self.player_tab.open(path):
            self.player_tab.play()

    def on_close(self):
        try:
            self.convert_tab.cancel.set()
            self.convert_tab.save_settings()
            self.player_tab.save_settings()
            self.settings.save()
        except Exception:
            pass
        self.player_tab.shutdown()
        self.mg_tab.shutdown()
        self.destroy()


def run_gui(files=None):
    if not TK_OK:
        sys.stderr.write("Tkinter n'est pas disponible dans cette installation de Python (paquet python3-tk).\n")
        return 2
    app = App(files)
    app.mainloop()
    return 0



# ============================================================================================
# AUTO-TESTS ET LIGNE DE COMMANDE
# ============================================================================================
def _selftest_frame(w, h, k):
    """Image de test déterministe (arithmétique entière, sans générateur aléatoire) au format BGR/DIB."""
    y, x = np.mgrid[0:h, 0:w].astype(np.int64)
    r = (x * 255 // max(w - 1, 1) + k * 13) & 255
    g = (y * 255 // max(h - 1, 1) + k * 7) & 255
    b = ((x * 3 + y * 5 + k * 29) ^ ((x * y) >> 3)) & 255
    n = ((x * 73856093) ^ (y * 19349663) ^ (k * 83492791)) & 255
    img = (np.stack([b, g, r], -1) + (n[..., None] >> 5)) & 255
    return img.astype(np.uint8)


def _selftest_audio(rate, channels, seconds):
    """Signal de test déterministe (triangles + créneaux) en entiers 16 bits entrelacés."""
    n = rate * seconds
    t = np.arange(n, dtype=np.int64)
    a = ((t * 440 * 4 // rate) % 4)             # forme en escalier
    tri = np.abs(((t * 440 * 2 * 1000 // rate) % 2000) - 1000) * 24 - 12000
    sq = np.where(((t * 660 // rate) % 2) == 0, 6000, -6000)
    left = tri + sq // 3 + a * 100
    right = (tri // 2) - sq // 2
    pcm = np.stack([left, right], 1)[:, :channels]
    return np.clip(pcm, -32768, 32767).astype("<i2")


# SHA-256 des sorties de l'encodeur obtenues avec les DLL d'ORIGINE sous Wine (identiques au code Python : tests T-003…T-011)
_KAT = {'amv_128x96': '61274a16b629f57e9c8d6c97', 'amv_160x120': '83e0b3a2cdded64a277e37b1', 'avi_128x96': '229871ff2eec7f9699347b5f', 'avi_208x176': '3290afe4b8271b38716ccd4c', 'audio_amv': 'f70857954c8f09b85878c070'}


def _sha(b):
    import hashlib
    return hashlib.sha256(b).hexdigest()[:24]


def selftest(verbose=True):
    """Auto-tests : tables, tests à réponse connue (sorties des DLL d'origine), aller-retour, structure des fichiers. Retourne True si tout passe."""
    results = []

    def check(name, cond, detail=""):
        results.append((name, bool(cond), detail))
        if verbose:
            print(("  OK    " if cond else "  ÉCHEC ") + name + (("  — " + detail) if detail else ""))

    # --- tables
    check("zigzag est une permutation de 0..63", sorted(ZIGZAG) == list(range(64)))
    check("quantification luma/chroma + réciproques", int(QY[0]) == 8 and int(QC[0]) == 9 and int(RY[0]) == 8193 and int(RC[4]) == 1311)
    for nm, bits, vals in (("DC luma", _DC_L_BITS, _DC_L_VALS), ("AC luma", _AC_L_BITS, _AC_L_VALS), ("DC chroma", _DC_C_BITS, _DC_C_VALS), ("AC chroma", _AC_C_BITS, _AC_C_VALS)):
        check("Huffman %s : %d codes, somme de Kraft ≤ 1" % (nm, sum(bits)), sum(bits) == len(vals) and sum(b / 2.0 ** (i + 1) for i, b in enumerate(bits)) <= 1.0)
    check("tables couleur IJG (Y de (255,255,255))", int((T_R_Y[255] + T_G_Y[255] + T_B_Y[255]) >> 14) == 255)
    # --- tests à réponse connue contre les DLL d'origine
    for key, (w, h, k) in _KAT_FRAMES.items():
        exp = _KAT.get(key)
        f = _selftest_frame(w, h, k)
        got = _sha(encode_frame(f) if key.startswith("amv") else encode_frame_avi(f))
        check("%s %dx%d identique à la DLL d'origine" % (key, w, h), exp is None or got == exp, "sha %s" % got)
    pcm = _selftest_audio(44100, 2, 1)
    enc = AmvAudioEncoder(44100, 2, 22050)
    blocks = []
    per = 44100 // 16
    pos = 0
    sec = pcm.reshape(-1).astype(np.int64).tolist()
    for i in range(16):
        n = per if i < 15 else 44100 - 15 * per
        blocks.append(enc.block(sec[pos * 2:(pos + n) * 2]))
        pos += n
    got = _sha(b"".join(blocks))
    check("audio AMV (44100 Hz stéréo → 22050 mono, 16 i/s) identique à la DLL", _KAT.get("audio_amv") in (None, got), "sha %s" % got)
    # --- aller-retour vidéo
    f = _selftest_frame(128, 96, 5)
    f = (f.astype(np.int32) // 8 * 8 + 64).clip(0, 255).astype(np.uint8)          # image douce
    d = decode_frame_bgr(encode_frame(f), 128, 96)
    mse = ((d.astype(float) - f.astype(float)) ** 2).mean()
    check("aller-retour vidéo AMV (PSNR > 18 dB)", 10 * np.log10(255 ** 2 / max(mse, 1e-9)) > 18, "%.1f dB" % (10 * np.log10(255 ** 2 / max(mse, 1e-9))))
    ch = encode_frame(f)
    check("décodeur Huffman rapide = décodeur de référence", bool((decode_frame_bgr(ch, 128, 96) == decode_frame_bgr_reference(ch, 128, 96)).all()))
    # --- aller-retour audio ADPCM
    pcm1 = _selftest_audio(22050, 1, 1)[:, 0].astype(np.int64).tolist()
    e2 = ImaAdpcmAmvEncoder()
    blk = _struct.pack("<hBBI", 0, 0, 0, len(pcm1)) + e2.encode(pcm1)
    dec = np.array(ImaAdpcmAmvDecoder.block(blk), dtype=np.float64)
    ref = np.array(pcm1, dtype=np.float64)
    snr = 10 * np.log10((ref ** 2).sum() / max(((ref - dec) ** 2).sum(), 1e-9))
    check("aller-retour ADPCM IMA (SNR > 12 dB)", snr > 12, "%.1f dB" % snr)
    # --- fichiers complets : écriture, lecture, vérification
    tmp = tempfile.mkdtemp(prefix="mpu_selftest_")
    try:
        frames = [_selftest_frame(96, 64, i) for i in range(16)]
        enc = AmvAudioEncoder(22050, 1, 22050)
        a = _selftest_audio(22050, 1, 1)[:, 0].astype(np.int64).tolist()
        per = 22050 // 16
        ach = [enc.block(a[i * per:(i + 1) * per if i < 15 else 22050]) for i in range(16)]
        vch = [encode_frame(fr) for fr in frames]
        p = os.path.join(tmp, "t.amv")
        with open(p, "wb") as fh:
            fh.write(build_amv_file(96, 64, 16, 22050, vch, ach, 1))
        ok, msgs = verify_file(p)
        check("fichier AMV : écriture + lecture + vérification de structure", ok, msgs[-1])
        m = open_media(p)
        check("fichier AMV : relecture (images, blocs audio)", m.nframes == 16 and len(m.audio) == 16 and m.width == 96 and m.height == 64)
        check("fichier AMV : décodage image 0 = décodage direct", bool((m.frame_bgr_dib(0) == decode_frame_bgr(vch[0], 96, 64)).all()))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    check("ffmpeg et ffprobe présents (nécessaires à la conversion)", bool(find_tool("ffmpeg") and find_tool("ffprobe")), find_tool("ffmpeg") or "absent")
    bad = [r for r in results if not r[1]]
    if verbose:
        print("\n%d contrôles, %d échec(s)" % (len(results), len(bad)))
    return not bad


_KAT_FRAMES = {"amv_128x96": (128, 96, 0), "amv_160x120": (160, 120, 1), "avi_128x96": (128, 96, 3), "avi_208x176": (208, 176, 2)}


def _parse_size(text):
    m = re.match(r"^\s*(\d+)\s*[xX×]\s*(\d+)\s*$", text)
    if not m:
        raise argparse.ArgumentTypeError("taille attendue : LARGEURxHAUTEUR (ex. 160x120)")
    return int(m.group(1)), int(m.group(2))


import argparse


def cli_main(argv):
    ap = argparse.ArgumentParser(prog="mpu_toolkit", description="%s %s — convertisseur AMV/AVI, lecteur et outils" % (APP_NAME, APP_VERSION))
    sub = ap.add_subparsers(dest="cmd")
    c = sub.add_parser("convert", help="convertir une vidéo en .amv ou .avi")
    c.add_argument("src")
    c.add_argument("dst", nargs="?")
    c.add_argument("--fmt", choices=("amv", "avi"))
    c.add_argument("--size", type=_parse_size, default=(160, 120))
    c.add_argument("--fps", type=int, default=30)
    c.add_argument("--audio-rate", type=int, default=22050, choices=AUDIO_RATES_AMV)
    c.add_argument("--orient", choices=ORIENTATIONS, default="normal")
    c.add_argument("--aspect", choices=ASPECT_MODES, default="stretch")
    c.add_argument("--start", default="0")
    c.add_argument("--end", default="0")
    c.add_argument("--audio-file", default="")
    c.add_argument("--gain", type=float, default=1.0)
    c.add_argument("--rgb565", action="store_true")
    c.add_argument("--no-insertwave", action="store_true")
    c.add_argument("--no-insertpic", action="store_true")
    c.add_argument("--vendor-updown-quirk", action="store_true")
    c.add_argument("--no-overwrite", action="store_true")
    i = sub.add_parser("info", help="propriétés et vérification d'un fichier AMV/AVI")
    i.add_argument("file")
    e = sub.add_parser("export", help="exporter un AMV/AVI vers mp4/avi/mkv")
    e.add_argument("src")
    e.add_argument("dst")
    f = sub.add_parser("frame", help="enregistrer une image (png/bmp)")
    f.add_argument("src")
    f.add_argument("dst")
    f.add_argument("--index", type=int, default=0)
    sub.add_parser("selftest", help="auto-tests internes")
    g = sub.add_parser("gui", help="interface graphique (défaut)")
    g.add_argument("files", nargs="*")
    a = ap.parse_args(argv)
    if a.cmd in (None, "gui"):
        return run_gui(getattr(a, "files", None))
    if a.cmd == "selftest":
        return 0 if selftest() else 1
    try:
        if a.cmd == "convert":
            fmt = a.fmt or (os.path.splitext(a.dst)[1].lower().lstrip(".") if a.dst else "amv")
            fmt = fmt if fmt in ("amv", "avi") else "amv"
            o = ConvertOptions(fmt=fmt, width=a.size[0], height=a.size[1], fps=a.fps, audio_rate=a.audio_rate, orientation=a.orient, aspect=a.aspect,
                               start=parse_time(a.start), end=parse_time(a.end), audio_file=a.audio_file, gain=a.gain, rgb565=a.rgb565,
                               insertwave=not a.no_insertwave, insertpic=not a.no_insertpic, overwrite=not a.no_overwrite,
                               vendor_updown_quirk=a.vendor_updown_quirk)
            dst = a.dst or default_output_path(a.src, o)
            last = [0.0]

            def prog(fr, txt):
                if time.time() - last[0] > 0.5 or fr >= 1.0:
                    last[0] = time.time()
                    sys.stderr.write("\r%5.1f %%  %s   " % (fr * 100, txt))
            r = convert_file(a.src, dst, o, progress=prog, log=lambda m: sys.stderr.write("\n" + m + "\n"))
            sys.stderr.write("\n")
            print("%s : %d images, %.1f s, %s, en %.1f s" % (dst, r["frames"], r["seconds"], fmt_size(r["bytes"]), r["elapsed"]))
            return 0
        if a.cmd == "info":
            m = open_media(a.file)
            for k, v in file_properties(m).items():
                print("%-30s %s" % (k + " :", v))
            ok, msgs = verify_file(a.file)
            print("\n".join(msgs))
            return 0 if ok else 1
        if a.cmd == "export":
            r = export_to_video(a.src, a.dst, progress=lambda fr, t: sys.stderr.write("\r%5.1f %%   " % (fr * 100)))
            sys.stderr.write("\n")
            print("%s : %d images, %s" % (a.dst, r["frames"], fmt_size(r["bytes"])))
            return 0
        if a.cmd == "frame":
            extract_frame(open_media(a.src), a.index, a.dst)
            print(a.dst)
            return 0
    except (ToolError, MediaFileError, ValueError, OSError) as e:
        sys.stderr.write("Erreur : %s\n" % e)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(cli_main(sys.argv[1:]))
