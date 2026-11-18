"""
Jogo de Samuel - Kivy (Pydroid 3 / Android)

Mapas: Casa (dentro e quintal), Mundo aberto e Mundo fechado.
Controles:
  Joystick (toque na metade esquerda) : andar
  Arrastar o dedo (metade direita)    : olhar em volta
  Botão redondo com seta              : pular (dá para subir em caixas, pedras e móveis)
  Botão de menu (canto de cima)       : pausar, trocar de mapa, sensibilidade, sair
Objetivo: pegar todas as gemas no menor tempo.
"""
import json
import os
import pickle
import tempfile
import socket
import threading
import time
from types import SimpleNamespace
import math
import random
import traceback

from kivy.app import App
from kivy.clock import Clock
from kivy.core.window import Window
from kivy.graphics import Color, Ellipse, Line, Mesh, Rectangle, RoundedRectangle
from kivy.graphics.texture import Texture
from kivy.uix.floatlayout import FloatLayout
from kivy.uix.label import Label
from kivy.uix.textinput import TextInput
from kivy.uix.widget import Widget

# ---------------- Configurações ----------------
ALTURA_OLHO = 1.7
ALTURA_JOGADOR = 1.8
RAIO = 0.45
VEL = 6.5
GRAV = 34.0
FORCA_PULO = 10.0
SENS_PADRAO = 0.22
Z_NEAR = 0.1
ORCAMENTO_BASE = 340     # máximo de polígonos desenhados por quadro

CEU_TOPO = (0.32, 0.53, 0.82)
CEU_MEIO = (0.52, 0.70, 0.88)
CEU_HORIZ = (0.68, 0.78, 0.86)   # também é a cor da neblina

MANGA = (0.30, 0.36, 0.46)
PELE = (0.91, 0.73, 0.60)


# ---------------- Utilidades de vetor / cor ----------------
def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def sub(a, b):
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def normalizar(v):
    c = math.sqrt(dot(v, v))
    if c < 1e-9:
        return None
    return (v[0] / c, v[1] / c, v[2] / c)


def misturar(a, b, t):
    t = max(0.0, min(1.0, t))
    return (a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t)


LUZ = normalizar((0.50, 0.70, 0.45))   # direção PARA o sol


def sombrear(cor, n):
    """Luz suave com temperatura de cor: sol quente nas faces iluminadas, ambiente fresco nas sombreadas
    (sem sombras projetadas)."""
    sol = max(0.0, dot(n, LUZ))
    hemi = 0.5 + 0.5 * n[1]
    k = min(0.98, 0.58 + 0.20 * hemi + 0.22 * sol)
    fr = 1.0 - sol           # quanto a face está "na sombra"
    r = cor[0] * k * (1.0 + 0.05 * sol - 0.04 * fr * (1.0 - hemi))
    g = cor[1] * k * (1.0 + 0.01 * sol + 0.01 * fr)
    b = cor[2] * k * (1.0 - 0.05 * sol + 0.05 * fr)
    lum = 0.30 * r + 0.59 * g + 0.11 * b          # cores mais suaves (menos saturadas)
    return (min(1.0, lum + (r - lum) * 0.86), min(1.0, lum + (g - lum) * 0.86), min(1.0, lum + (b - lum) * 0.86))


# ---------------- Texturas geradas por código ----------------
# ======================= TEXTURAS (geradas por código, 128x128, sem arquivos) =======================
# Todas repetem sem emenda (tileáveis). As "neutras" (casca, folhas, rocha, terra, grama) são multiplicadas
# pela cor do objeto, então servem para qualquer tom de verde/marrom/cinza.
M = 128
VERSAO_TEX = 4

MEDIAS = {
    'tijolo': (0.66, 0.38, 0.30), 'pedra': (0.50, 0.49, 0.51), 'madeira': (0.68, 0.45, 0.25),
    'ladrilho': (0.76, 0.79, 0.75), 'reboco': (0.89, 0.87, 0.81), 'concreto': (0.57, 0.58, 0.58),
    'grama': (0.71, 0.78, 0.63), 'terra': (0.73, 0.67, 0.59), 'telhas': (0.53, 0.26, 0.19),
    'casca': (0.60, 0.58, 0.56), 'folhas': (0.56, 0.61, 0.53), 'rocha': (0.74, 0.74, 0.75),
    'tecido': (0.80, 0.80, 0.80), 'jeans': (0.73, 0.73, 0.73), 'cabelo': (0.62, 0.62, 0.62),
    'pele': (0.91, 0.90, 0.88), 'couro': (0.56, 0.56, 0.56),
}


def _campo(rng, g):
    """Ruído de valor suave e tileável com g células por lado -> lista M*M em [-1, 1]."""
    lat = [[rng.uniform(-1.0, 1.0) for _ in range(g)] for _ in range(g)]
    tab = []
    for x in range(M):
        f = x * g / float(M)
        i0 = int(f) % g
        t = f - int(f)
        tab.append((i0, (i0 + 1) % g, t * t * (3.0 - 2.0 * t)))
    out = [0.0] * (M * M)
    for y in range(M):
        y0, y1, ty = tab[y]
        r0, r1 = lat[y0], lat[y1]
        base = y * M
        for x in range(M):
            x0, x1, tx = tab[x]
            a = r0[x0] + (r0[x1] - r0[x0]) * tx
            b = r1[x0] + (r1[x1] - r1[x0]) * tx
            out[base + x] = a + (b - a) * ty
    return out


def _fbm(rng, oit=((4, 1.0), (8, 0.55), (16, 0.3), (32, 0.16))):
    tot = sum(w for _, w in oit)
    soma = None
    for g, w in oit:
        c = _campo(rng, g)
        soma = [w * v for v in c] if soma is None else [s + w * v for s, v in zip(soma, c)]
    return [s / tot for s in soma]


def _c(v):
    return 0 if v < 0 else (255 if v > 255 else int(v))


def _fim(buf):
    n = len(buf) // 3
    media = (sum(buf[0::3]) / (255.0 * n), sum(buf[1::3]) / (255.0 * n), sum(buf[2::3]) / (255.0 * n))
    return bytes(buf), media


def _pontos(rng, n):
    """Pontos jitterados em grade n x n (para células de pedra/rocha, tileável)."""
    pts = []
    for j in range(n):
        for i in range(n):
            pts.append(((i + rng.uniform(0.15, 0.85)) * M / n, (j + rng.uniform(0.15, 0.85)) * M / n))
    return pts


def _voronoi(rng, n):
    """Para cada pixel: (índice da célula, distância à borda aproximada d2-d1). Tileável."""
    pts = _pontos(rng, n)
    cel = M / float(n)
    cid = [0] * (M * M)
    borda = [0.0] * (M * M)
    for y in range(M):
        cj = int(y / cel)
        for x in range(M):
            ci = int(x / cel)
            d1 = d2 = 1e9
            k1 = 0
            for dj in (-1, 0, 1):
                for di in (-1, 0, 1):
                    jj, ii = (cj + dj) % n, (ci + di) % n
                    px, py = pts[jj * n + ii]
                    if ci + di < 0:
                        px -= M
                    elif ci + di >= n:
                        px += M
                    if cj + dj < 0:
                        py -= M
                    elif cj + dj >= n:
                        py += M
                    d = (px - x) * (px - x) + (py - y) * (py - y)
                    if d < d1:
                        d2, d1, k1 = d1, d, jj * n + ii
                    elif d < d2:
                        d2 = d
            cid[y * M + x] = k1
            borda[y * M + x] = math.sqrt(d2) - math.sqrt(d1)
    return cid, borda


def gerar_tijolo(rng, F):
    buf = bytearray(M * M * 3)
    LH, LW = 16, 32
    tons = {}
    for y in range(M):
        fila = y // LH
        desl = LW // 2 if fila % 2 else 0
        yl = y % LH
        for x in range(M):
            xx = (x + desl) % M
            xl = xx % LW
            col = xx // LW
            n = F[0][y * M + x]
            i = (y * M + x) * 3
            if yl < 2 or xl < 2:                     # argamassa
                v = 176 + n * 14 + rng.randint(-6, 6)
                sombra = 0
                if yl == 2 or xl == 2:
                    sombra = -18
                _ = sombra
                buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v - 5), _c(v - 14)
            else:
                t = tons.get((fila, col))
                if t is None:
                    t = (rng.uniform(-20, 20), rng.uniform(-8, 8))
                    tons[(fila, col)] = t
                r, g, b = 172 + t[0], 84 + t[0] * 0.55 + t[1], 62 + t[0] * 0.45
                r, g, b = r + n * 16, g + n * 10, b + n * 8
                g2 = F[1][y * M + x]
                r, g, b = r + g2 * 9, g + g2 * 6, b + g2 * 5
                if yl == 2:                            # topo claro
                    r, g, b = r + 22, g + 16, b + 12
                if yl == LH - 1 or xl == LW - 1:       # base e lado na sombra
                    r, g, b = r - 28, g - 20, b - 16
                if rng.random() < 0.012:                # lascas escuras
                    r, g, b = r - 40, g - 30, b - 24
                s = rng.randint(-7, 7)
                buf[i], buf[i + 1], buf[i + 2] = _c(r + s), _c(g + s), _c(b + s)
    return _fim(buf)


def gerar_pedra(rng, F):
    buf = bytearray(M * M * 3)
    cid, borda = _voronoi(rng, 4)
    tom = [rng.uniform(-18, 18) for _ in range(16)]
    for y in range(M):
        for x in range(M):
            k = y * M + x
            n = F[0][k]
            b = borda[k] + n * 1.6
            v = 148 + tom[cid[k]] + n * 20 + F[1][k] * 9 + rng.randint(-6, 6)
            if b < 5.0:
                t = max(0.0, b) / 5.0                    # junta escura entre as pedras, com bisel
                v = v * (0.40 + 0.60 * t) - 6
            elif b < 9.0:
                v += 10 * (1 - (b - 5.0) / 4.0)           # leve brilho na quina
            i = k * 3
            buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v - 1), _c(v + 3)
    return _fim(buf)


def gerar_madeira(rng, F):
    buf = bytearray(M * M * 3)
    LH = 32
    tons = [rng.uniform(-18, 18) for _ in range(M // LH)]
    junta = [rng.randrange(M) for _ in range(M // LH)]
    nos = [(rng.randrange(M), rng.randrange(M), rng.uniform(5, 9)) for _ in range(3)]
    for y in range(M):
        p = y // LH
        yl = y % LH
        for x in range(M):
            k = y * M + x
            gr = 0.5 + 0.5 * math.sin(y * 0.9 + 6.0 * F[2][((y % M) * M + (x // 3 * 3) % M)] + F[0][k] * 3.0)
            gr2 = 0.5 + 0.5 * math.sin(y * 2.3 + 9.0 * F[1][k])
            v = 150 + tons[p] + gr * 22 + gr2 * 8 - 14
            r, g, b = v + 28, v * 0.72 + 10, v * 0.42 + 4
            for (kx, ky, kr) in nos:
                dx = min(abs(x - kx), M - abs(x - kx))
                dy = min(abs(y - ky), M - abs(y - ky))
                d = math.sqrt(dx * dx * 0.5 + dy * dy * 2.0)
                if d < kr * 2:
                    a = 0.5 + 0.5 * math.sin(d * 1.7)
                    f = 1.0 - 0.28 * a * (1 - d / (kr * 2))
                    r, g, b = r * f, g * f, b * f
            if yl < 2:                                    # fresta entre as tábuas
                f = 0.45 if yl == 0 else 0.78
                r, g, b = r * f, g * f, b * f
            elif x == junta[p] or x == (junta[p] + 1) % M:  # emenda de topo
                r, g, b = r * 0.55, g * 0.55, b * 0.55
            s = rng.randint(-4, 4)
            i = k * 3
            buf[i], buf[i + 1], buf[i + 2] = _c(r + s), _c(g + s), _c(b + s)
    return _fim(buf)


def gerar_ladrilho(rng, F):
    buf = bytearray(M * M * 3)
    L = 32
    for y in range(M):
        for x in range(M):
            k = y * M + x
            xl, yl = x % L, y % L
            i = k * 3
            if xl < 2 or yl < 2:
                v = 150 + F[1][k] * 10 + rng.randint(-5, 5)
                buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v - 2), _c(v - 8)
                continue
            par = ((x // L) + (y // L)) % 2
            r, g, b = (228, 226, 214) if par == 0 else (170, 192, 184)
            m = F[0][k] * 7 + F[2][k] * 4
            brilho = 14 * (1.0 - (xl + yl) / (2.0 * L)) - 4          # brilho diagonal de esmalte
            r, g, b = r + m + brilho, g + m + brilho, b + m + brilho
            if xl == 2 or yl == 2:
                r, g, b = r + 14, g + 14, b + 14
            if xl == L - 1 or yl == L - 1:
                r, g, b = r - 26, g - 26, b - 24
            if rng.random() < 0.004:
                r, g, b = r - 30, g - 30, b - 30
            buf[i], buf[i + 1], buf[i + 2] = _c(r), _c(g), _c(b)
    return _fim(buf)


def gerar_reboco(rng, F):
    buf = bytearray(M * M * 3)
    for k in range(M * M):
        n = F[0][k] * 6 + F[1][k] * 5 + F[2][k] * 3
        s = rng.randint(-6, 6)
        v = 0.0
        if rng.random() < 0.006:
            v = -22.0
        i = k * 3
        buf[i], buf[i + 1], buf[i + 2] = _c(229 + n + s + v), _c(223 + n + s + v), _c(208 + n + s + v)
    return _fim(buf)


def gerar_concreto(rng, F):
    buf = bytearray(M * M * 3)
    poros = []
    for _ in range(140):
        poros.append((rng.randrange(M), rng.randrange(M), rng.choice((1, 1, 1, 2))))
    marca = {}
    for (px_, py_, r) in poros:
        for dy in range(-r, r + 1):
            for dx in range(-r, r + 1):
                if dx * dx + dy * dy <= r * r:
                    marca[((py_ + dy) % M) * M + (px_ + dx) % M] = 1
    for y in range(M):
        for x in range(M):
            k = y * M + x
            v = 152 + F[0][k] * 16 + F[1][k] * 9 + F[2][k] * 4 + rng.randint(-5, 5)
            if k in marca:
                v -= 34
            if y < 2:                                     # junta de forma
                v -= 26 if y == 0 else 10
            if (x % 64 in (30, 31, 32, 33)) and (y % 64 in (30, 31, 32, 33)):   # marca dos pinos
                v -= 22
            i = k * 3
            buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v + 1), _c(v + 1)
    return _fim(buf)


def gerar_grama(rng, F):
    buf = bytearray(M * M * 3)
    for k in range(M * M):
        v = 196 + F[0][k] * 20 + F[1][k] * 12 + rng.randint(-9, 9)
        i = k * 3
        buf[i], buf[i + 1], buf[i + 2] = _c(v * 0.94), _c(v + 6), _c(v * 0.84)
    for _ in range(900):                                    # folhinhas
        x, y = rng.randrange(M), rng.randrange(M)
        comp = rng.randint(4, 10)
        lean = rng.uniform(-0.35, 0.35)
        tom = rng.uniform(-1.0, 1.0)
        for s in range(comp):
            xx = int(x + lean * s) % M
            yy = (y + s) % M
            f = s / float(comp)                              # base escura -> ponta clara
            v = (150 + 95 * f + tom * 18)
            i = (yy * M + xx) * 3
            buf[i], buf[i + 1], buf[i + 2] = _c(v * 0.93), _c(v + 5), _c(v * 0.82)
    for _ in range(14):                                     # florzinhas/trevos
        x, y = rng.randrange(M), rng.randrange(M)
        cor = rng.choice(((255, 255, 240), (255, 238, 150)))
        for dx, dy in ((0, 0), (1, 0), (0, 1), (1, 1)):
            i = (((y + dy) % M) * M + (x + dx) % M) * 3
            buf[i], buf[i + 1], buf[i + 2] = cor
    return _fim(buf)


def gerar_terra(rng, F):
    buf = bytearray(M * M * 3)
    for k in range(M * M):
        v = 190 + F[0][k] * 22 + F[1][k] * 14 + F[2][k] * 6 + rng.randint(-7, 7)
        i = k * 3
        buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v * 0.92), _c(v * 0.80)
    for _ in range(120):                                    # pedrinhas
        x, y, r = rng.randrange(M), rng.randrange(M), rng.choice((1, 2, 2, 3))
        tom = rng.uniform(-35, 45)
        for dy in range(-r, r + 1):
            for dx in range(-r, r + 1):
                if dx * dx + dy * dy <= r * r + 1:
                    f = 1.0 + (0.18 if dy < 0 else -0.18)
                    i = (((y + dy) % M) * M + (x + dx) % M) * 3
                    v = (190 + tom) * f
                    buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v * 0.93), _c(v * 0.84)
    return _fim(buf)


def gerar_telhas(rng, F):
    buf = bytearray(M * M * 3)
    LH, LW = 16, 32
    tons = {}
    for y in range(M):
        fila = y // LH
        yl = y % LH
        desl = LW // 2 if fila % 2 else 0
        for x in range(M):
            xx = (x + desl) % M
            xl = xx % LW
            col = xx // LW
            t = tons.get((fila, col))
            if t is None:
                t = rng.uniform(-16, 16)
                tons[(fila, col)] = t
            k = y * M + x
            f = yl / float(LH - 1)
            sombra = 1.0 - 0.42 * (f ** 3)                    # cada telha escurece até a borda de baixo
            canal = 1.0 - 0.18 * abs(math.sin(xl * math.pi / LW * 2.0))   # ondulação da telha
            r, g, b = 184 + t, 92 + t * 0.6, 66 + t * 0.4
            m = F[0][k] * 10 + F[1][k] * 5
            r, g, b = (r + m) * sombra * canal, (g + m * 0.7) * sombra * canal, (b + m * 0.5) * sombra * canal
            if yl == LH - 1:
                r, g, b = r * 0.45, g * 0.45, b * 0.45
            if xl == LW - 1 or xl == 0:
                r, g, b = r * 0.78, g * 0.78, b * 0.78
            if rng.random() < 0.01:                            # limo/manchas claras
                r, g, b = r * 0.8 + 14, g * 0.85 + 18, b * 0.8 + 10
            s = rng.randint(-5, 5)
            i = k * 3
            buf[i], buf[i + 1], buf[i + 2] = _c(r + s), _c(g + s), _c(b + s)
    return _fim(buf)


def gerar_casca(rng, F):
    buf = bytearray(M * M * 3)
    for y in range(M):
        for x in range(M):
            k = y * M + x
            sulco = abs(math.sin(x * 2.0 * math.pi * 7.0 / M + 2.6 * F[0][k] + 1.2 * F[1][k]))   # sulcos verticais ondulados
            v = 170 + F[1][k] * 18 + F[2][k] * 10 - (1.0 - sulco) ** 2 * 70 + rng.randint(-8, 8)
            i = k * 3
            buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v * 0.96), _c(v * 0.92)
    return _fim(buf)


def gerar_folhas(rng, F):
    buf = bytearray(M * M * 3)
    for k in range(M * M):
        v = 128 + F[0][k] * 26 + F[1][k] * 14
        i = k * 3
        buf[i], buf[i + 1], buf[i + 2] = _c(v * 0.92), _c(v), _c(v * 0.88)
    for _ in range(260):                                    # folhas sobrepostas (clara em cima, escura embaixo)
        cx, cy = rng.randrange(M), rng.randrange(M)
        rx, ry = rng.uniform(2.5, 5.0), rng.uniform(4.0, 7.0)
        ang = rng.uniform(0, math.pi)
        ca, sa = math.cos(ang), math.sin(ang)
        tom = rng.uniform(150, 250)
        for dy in range(-8, 9):
            for dx in range(-8, 9):
                u = (dx * ca + dy * sa) / rx
                w = (-dx * sa + dy * ca) / ry
                d = u * u + w * w
                if d <= 1.0:
                    f = 1.0 - 0.30 * ((w + 1) / 2.0)           # gradiente na folha
                    if abs(u) < 0.12:
                        f += 0.12                              # nervura
                    v = tom * f
                    i = (((cy + dy) % M) * M + (cx + dx) % M) * 3
                    buf[i], buf[i + 1], buf[i + 2] = _c(v * 0.92), _c(v), _c(v * 0.86)
    return _fim(buf)


def gerar_rocha(rng, F):
    buf = bytearray(M * M * 3)
    cid, borda = _voronoi(rng, 3)
    for y in range(M):
        for x in range(M):
            k = y * M + x
            n = F[0][k] * 30 + F[1][k] * 16 + F[2][k] * 7
            v = 200 + n + rng.randint(-8, 8)
            b = borda[k] + F[1][k] * 2.0
            if b < 3.0:
                v *= 0.55 + 0.15 * max(0.0, b)               # rachaduras
            if rng.random() < 0.006:
                v += 40                                      # grãos de mica
            i = k * 3
            buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v), _c(v + 2)
    return _fim(buf)


def gerar_tecido(rng, F):
    buf = bytearray(M * M * 3)
    for y in range(M):
        for x in range(M):
            k = y * M + x
            fio = math.sin(x * 2.0 * math.pi * 16 / M) * math.sin(y * 2.0 * math.pi * 16 / M)
            v = 205 + fio * 20 + F[2][k] * 10 + rng.randint(-5, 5)
            i = k * 3
            buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v), _c(v)
    return _fim(buf)


def gerar_jeans(rng, F):
    buf = bytearray(M * M * 3)
    for y in range(M):
        for x in range(M):
            k = y * M + x
            tw = math.sin((x + y) * 2.0 * math.pi * 24 / M)          # sarja diagonal
            v = 185 + tw * 22 + F[1][k] * 22 + F[2][k] * 8 + rng.randint(-7, 7)
            if (x * 3 + y * 5) % 61 == 0:
                v += 28                                                # fios claros desgastados
            i = k * 3
            buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v), _c(v)
    return _fim(buf)


def gerar_cabelo(rng, F):
    buf = bytearray(M * M * 3)
    for y in range(M):
        for x in range(M):
            k = y * M + x
            fio = math.sin(x * 2.0 * math.pi * 22 / M + 3.0 * F[0][k] + 1.5 * F[1][k])
            brilho = max(0.0, math.sin(y * 2.0 * math.pi * 2 / M + 2.0 * F[1][k])) ** 3
            v = 150 + fio * 34 + brilho * 40 + rng.randint(-8, 8)
            i = k * 3
            buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v), _c(v)
    return _fim(buf)


def gerar_pele(rng, F):
    buf = bytearray(M * M * 3)
    for k in range(M * M):
        v = 232 + F[1][k] * 10 + F[2][k] * 6 + rng.randint(-4, 4)
        i = k * 3
        buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v * 0.985), _c(v * 0.97)
    return _fim(buf)


def gerar_couro(rng, F):
    buf = bytearray(M * M * 3)
    for k in range(M * M):
        v = 150 + F[0][k] * 24 + F[2][k] * 22 + rng.randint(-10, 10)
        if F[1][k] > 0.62:
            v -= 30                                                    # vincos do couro
        i = k * 3
        buf[i], buf[i + 1], buf[i + 2] = _c(v), _c(v), _c(v)
    return _fim(buf)


GERADORES = (('tijolo', gerar_tijolo), ('pedra', gerar_pedra), ('madeira', gerar_madeira),
             ('ladrilho', gerar_ladrilho), ('reboco', gerar_reboco), ('concreto', gerar_concreto),
             ('grama', gerar_grama), ('terra', gerar_terra), ('telhas', gerar_telhas),
             ('casca', gerar_casca), ('folhas', gerar_folhas), ('rocha', gerar_rocha),
             ('tecido', gerar_tecido), ('jeans', gerar_jeans), ('cabelo', gerar_cabelo), ('pele', gerar_pele),
             ('couro', gerar_couro))


def caminho_cache():
    for base in (os.path.dirname(os.path.abspath(__file__)) if '__file__' in globals() else None,
                 os.path.expanduser('~'), tempfile.gettempdir()):
        if base and os.access(base, os.W_OK):
            return os.path.join(base, '.jogo_samuel_tex_v%d.bin' % VERSAO_TEX)
    return None


def gerar_todas(progresso=None):
    """Gera todas as texturas (bytes RGB). Demora na 1ª vez; o resultado vai para o cache em disco."""
    rng = random.Random(7)
    F = [_fbm(rng), _fbm(rng), _fbm(rng, ((8, 1.0), (16, 0.5), (32, 0.25)))]
    res = {}
    for nome, fn in GERADORES:
        res[nome] = fn(rng, F)
        if progresso:
            progresso(nome, res[nome])
    return res


def ler_cache():
    try:
        c = caminho_cache()
        if c and os.path.exists(c):
            with open(c, 'rb') as f:
                d = pickle.load(f)
            if all(n in d and len(d[n][0]) == M * M * 3 for n, _ in GERADORES):
                return d
    except Exception:
        pass
    return None


def gravar_cache(d):
    try:
        c = caminho_cache()
        if c:
            with open(c + '.tmp', 'wb') as f:
                pickle.dump(d, f, protocol=2)
            os.replace(c + '.tmp', c)
    except Exception:
        pass


def textura_gl(dados):
    """Cria a textura do Kivy (com mipmap, para não cintilar de longe). Retorna None se falhar."""
    try:
        try:
            tex = Texture.create(size=(M, M), colorfmt='rgb', mipmap=True)
            tex.blit_buffer(dados, colorfmt='rgb', bufferfmt='ubyte')
            tex.min_filter = 'linear_mipmap_linear'
            tex.mag_filter = 'linear'
        except Exception:
            tex = Texture.create(size=(M, M), colorfmt='rgb')
            tex.blit_buffer(dados, colorfmt='rgb', bufferfmt='ubyte')
        tex.wrap = 'repeat'
        return tex
    except Exception:
        return None
# ======================= MÚSICA (sintetizada por código; vira um .wav no cache e toca em loop) =======================
import array
import wave

SR = 16000
VERSAO_MUSICA = 1
NOTAS = {'C': 0, 'D': 2, 'E': 4, 'F': 5, 'G': 7, 'A': 9, 'B': 11}


def _freq(nome, oitava):
    """'C#' ou 'Bb' e oitava -> Hz (A4 = 440)."""
    n = NOTAS[nome[0]] + (1 if '#' in nome else 0) - (1 if 'b' in nome[1:] else 0)
    return 440.0 * 2.0 ** ((n - 9 + 12 * (oitava - 4)) / 12.0)


FAIXAS = {
    # nome: (bpm, [acordes por compasso: (raiz, oitava_baixo, [notas (nome, oitava)])], estilo)
    'campo': (72, [
        ('C', [('C', 3), ('E', 3), ('G', 3), ('B', 3)]), ('A', [('A', 2), ('E', 3), ('G', 3), ('C', 4)]),
        ('F', [('F', 2), ('C', 3), ('E', 3), ('A', 3)]), ('G', [('G', 2), ('D', 3), ('F', 3), ('B', 3)]),
        ('C', [('C', 3), ('E', 3), ('G', 3), ('D', 4)]), ('A', [('A', 2), ('E', 3), ('G', 3), ('C', 4)]),
        ('F', [('F', 2), ('C', 3), ('A', 3), ('E', 4)]), ('G', [('G', 2), ('D', 3), ('G', 3), ('B', 3)]),
    ], 'brilhante'),
    'casa': (58, [
        ('F', [('F', 2), ('C', 3), ('E', 3), ('A', 3)]), ('E', [('E', 2), ('B', 2), ('D', 3), ('G', 3)]),
        ('D', [('D', 2), ('A', 2), ('C', 3), ('F', 3)]), ('C', [('C', 2), ('G', 2), ('B', 2), ('E', 3)]),
        ('F', [('F', 2), ('C', 3), ('E', 3), ('A', 3)]), ('E', [('E', 2), ('B', 2), ('D', 3), ('G', 3)]),
        ('A', [('A', 2), ('E', 3), ('G', 3), ('C', 4)]), ('G', [('G', 2), ('D', 3), ('F', 3), ('B', 3)]),
    ], 'aconchegante'),
}


def _somar(buf, ini, dados, ganho=1.0):
    """Soma 'dados' em buf a partir de 'ini', com volta ao começo (loop sem emenda)."""
    n = len(buf)
    j = ini % n
    for v in dados:
        buf[j] += v * ganho
        j += 1
        if j >= n:
            j = 0


def _nota(freq, dur, ataque, solta, harm, vibr=0.0, curva=None):
    """Uma nota: soma de harmônicos com envelope. harm = [(multiplo, amplitude), ...]."""
    n = int(dur * SR)
    saida = [0.0] * n
    two = 2.0 * math.pi / SR
    na, ns = max(1, int(ataque * SR)), max(1, int(solta * SR))
    fases = [freq * m * two for m, _ in harm]
    amps = [a for _, a in harm]
    for i in range(n):
        if i < na:
            e = i / float(na)
            e = e * e * (3 - 2 * e)
        elif i > n - ns:
            e = (n - i) / float(ns)
            e = e * e * (3 - 2 * e)
        else:
            e = 1.0
        if curva is not None:
            e *= math.exp(-curva * i / SR)
        v = vibr * math.sin(i * two * 5.0) if vibr else 0.0
        s = 0.0
        for fz, a in zip(fases, amps):
            s += a * math.sin(fz * i + v)
        saida[i] = s * e
        if i % 4000 == 3999:
            time.sleep(0.001)          # deixa o jogo respirar enquanto a música é gerada
    return saida


def compor(nome):
    bpm, compassos, estilo = FAIXAS[nome]
    rng = random.Random(hash(nome) & 0xFFFF)
    batida = 60.0 / bpm
    comp = 4 * batida
    total = int(comp * len(compassos) * SR)
    buf = [0.0] * total
    cache = {}

    def nota(key, *a, **k):
        if key not in cache:
            cache[key] = _nota(*a, **k)
        return cache[key]

    for idx, (raiz, notas) in enumerate(compassos):
        t0 = int(idx * comp * SR)
        # pad (acorde sustentado, atacando devagar, com leve desafinação para "abrir" o som)
        for (nm, oc) in notas:
            f = _freq(nm, oc)
            d = nota(('pad', nm, oc), f, comp + 1.6, 1.1, 1.3, [(1, 1.0), (2, 0.25), (1.004, 0.6)])
            _somar(buf, t0 - int(0.5 * SR), d, 0.060 if estilo == 'brilhante' else 0.070)
        # baixo
        nm, oc = notas[0]
        d = nota(('baixo', nm, oc), _freq(nm, oc), comp * 0.98, 0.04, 0.6, [(1, 1.0), (2, 0.18)])
        _somar(buf, t0, d, 0.15)
        # arpejo (plucks que decaem) com algumas pausas para respirar
        padrao = [0, 1, 2, 3, 2, 1, 2, 1] if estilo == 'brilhante' else [0, 2, 1, 3, 1, 2, 3, 2]
        passo = batida / 2.0
        for k, p in enumerate(padrao):
            if rng.random() < (0.12 if estilo == 'brilhante' else 0.28):
                continue
            nm, oc = notas[p]
            oc2 = oc + (1 if estilo == 'brilhante' else 2)
            f = _freq(nm, oc2)
            if estilo == 'brilhante':
                d = nota(('pl', nm, oc2), f, 1.4, 0.004, 0.5, [(1, 1.0), (2, 0.28), (3, 0.08)], 0.0, 4.2)
                g = 0.085 * (0.75 + 0.25 * (k % 2 == 0))
            else:      # caixinha de música: mais aguda e com cauda longa
                d = nota(('cx', nm, oc2), f, 2.0, 0.004, 0.8, [(1, 1.0), (2.76, 0.12), (4.1, 0.05)], 0.0, 2.6)
                g = 0.10
            _somar(buf, t0 + int(k * passo * SR), d, g)
        # melodia esparsa nos compassos pares
        if idx % 2 == 0:
            nm, oc = notas[3]
            f = _freq(nm, oc + 1)
            d = nota(('mel', nm, oc), f, batida * 3.2, 0.5, 0.9, [(1, 1.0), (2, 0.12)], 0.9)
            _somar(buf, t0 + int(batida * SR), d, 0.05)
    # reverberação simples (dois pentes) aplicada duas vezes seguidas para a cauda dar a volta no loop
    for atraso, fb in ((int(0.053 * SR), 0.42), (int(0.089 * SR), 0.36)):
        buf2 = buf + buf
        for i in range(atraso, len(buf2)):
            buf2[i] += buf2[i - atraso] * fb
        buf = buf2[total:]
    pico = max(0.001, max(abs(v) for v in buf))
    ganho = 0.82 * 32767.0 / pico
    return array.array('h', [int(v * ganho) for v in buf])


def caminho_musica(nome):
    base = caminho_cache()
    if not base:
        return None
    return os.path.join(os.path.dirname(base), '.jogo_samuel_musica_%s_v%d.wav' % (nome, VERSAO_MUSICA))


def gravar_wav(caminho, amostras):
    with wave.open(caminho + '.tmp', 'wb') as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(SR)
        w.writeframes(amostras.tobytes())
    os.replace(caminho + '.tmp', caminho)


class Musica:
    """Toca a trilha da fase em loop, em 3 volumes (e desligada). A trilha é gerada em segundo plano na 1ª vez."""
    NIVEIS = {'desl': 0.0, 'baixa': 0.16, 'media': 0.38, 'alta': 0.75}

    def __init__(self):
        self.faixa = None            # o que deveria estar tocando
        self.tocando = None
        self.som = None
        self.nivel = 'baixa'
        self.pronto = {}
        self.gerando = False
        self.falhou = False
        self._carregador = None
        try:
            from kivy.core.audio import SoundLoader
            self._carregador = SoundLoader
        except Exception:
            self._carregador = None
        for nome in FAIXAS:
            c = caminho_musica(nome)
            if c and os.path.exists(c):
                self.pronto[nome] = c
        if len(self.pronto) < len(FAIXAS):
            self.gerando = True
            threading.Thread(target=self._gerar, daemon=True).start()

    def _gerar(self):
        try:
            for nome in FAIXAS:
                if nome in self.pronto:
                    continue
                c = caminho_musica(nome)
                if not c:
                    continue
                gravar_wav(c, compor(nome))
                self.pronto[nome] = c
        except Exception:
            self.falhou = True
        self.gerando = False

    def trocar(self, faixa):
        self.faixa = faixa

    def volume(self, nivel):
        self.nivel = nivel
        if self.som is not None:
            try:
                self.som.volume = self.NIVEIS.get(nivel, 0.16)
            except Exception:
                pass

    def tick(self):
        """Chamado de tempos em tempos pelo loop do jogo."""
        if self._carregador is None or self.falhou:
            return
        vol = self.NIVEIS.get(self.nivel, 0.16)
        if vol <= 0.0 or self.faixa is None:
            if self.som is not None:
                try:
                    self.som.stop()
                except Exception:
                    pass
                self.som, self.tocando = None, None
            return
        if self.tocando != self.faixa and self.faixa in self.pronto:
            try:
                if self.som is not None:
                    self.som.stop()
                self.som = self._carregador.load(self.pronto[self.faixa])
                if self.som is not None:
                    self.som.loop = True
                    self.som.volume = vol
                    self.som.play()
                    self.tocando = self.faixa
                else:
                    self.falhou = True
            except Exception:
                self.falhou = True
        elif self.som is not None:
            try:
                self.som.volume = vol
                if self.som.state != 'play':
                    self.som.play()
            except Exception:
                pass
# ======================= EFEITOS SONOROS (sintetizados por código) =======================
VERSAO_SFX = 1
SR_FX = 16000


def _env_exp(n, taxa):
    return [math.exp(-taxa * i / SR_FX) for i in range(n)]


def _passa_baixa(x, a):
    y, saida = 0.0, []
    for v in x:
        y += a * (v - y)
        saida.append(y)
    return saida


def _ruido(rng, n):
    return [rng.uniform(-1.0, 1.0) for _ in range(n)]


def _fx_arbusto():
    rng = random.Random(7)
    n = int(0.42 * SR_FX)
    r = _ruido(rng, n)
    b = [v - w for v, w in zip(r, _passa_baixa(r, 0.12))]          # tira os graves
    b = _passa_baixa(b, 0.55)
    env = [0.0] * n
    for _ in range(9):                                              # vários "farfalhos" curtos
        t0 = rng.randrange(0, int(0.28 * SR_FX))
        amp = rng.uniform(0.4, 1.0)
        for i in range(t0, min(n, t0 + int(0.12 * SR_FX))):
            env[i] += amp * math.exp(-22.0 * (i - t0) / SR_FX)
    return [v * min(1.0, e) * (1.0 - i / n) for i, (v, e) in enumerate(zip(b, env))]


def _fx_quebra():
    rng = random.Random(11)
    n = int(0.55 * SR_FX)
    out = [0.0] * n
    for (t0, amp, f0) in ((0.0, 1.0, 150.0), (0.07, 0.7, 210.0), (0.15, 0.5, 120.0)):
        s0 = int(t0 * SR_FX)
        for i in range(s0, n):
            t = (i - s0) / SR_FX
            click = rng.uniform(-1, 1) * math.exp(-60.0 * t)
            corpo = math.sin(2 * math.pi * f0 * t) * math.exp(-14.0 * t)
            out[i] += amp * (0.55 * click + 0.75 * corpo)
    out = _passa_baixa(out, 0.6)
    for i in range(int(0.30 * SR_FX), n):                          # lascas caindo
        if rng.random() < 0.004:
            for j in range(i, min(n, i + 90)):
                out[j] += rng.uniform(-1, 1) * 0.25 * math.exp(-0.06 * (j - i))
    return out


def _fx_golpe():
    rng = random.Random(5)
    n = int(0.2 * SR_FX)
    return [(0.5 * rng.uniform(-1, 1) * math.exp(-80.0 * i / SR_FX) + 0.9 * math.sin(2 * math.pi * 105 * i / SR_FX) * math.exp(-26.0 * i / SR_FX)) for i in range(n)]


def _fx_pegar():
    n = int(0.16 * SR_FX)
    return [math.sin(2 * math.pi * (480 + 520 * (i / n)) * i / SR_FX) * math.sin(math.pi * i / n) for i in range(n)]


def _fx_conquista():
    n = int(0.9 * SR_FX)
    out = [0.0] * n
    for t0, f in ((0.0, 660.0), (0.14, 880.0), (0.30, 1320.0)):
        for i in range(int(t0 * SR_FX), n):
            t = (i / SR_FX) - t0
            out[i] += (math.sin(2 * math.pi * f * t) + 0.3 * math.sin(4 * math.pi * f * t)) * math.exp(-5.0 * t) * 0.45
    return out


def _fx_toc():
    rng = random.Random(3)
    n = int(0.15 * SR_FX)
    return [(0.35 * rng.uniform(-1, 1) * math.exp(-90.0 * i / SR_FX) + math.sin(2 * math.pi * 190 * i / SR_FX) * math.exp(-30.0 * i / SR_FX)) for i in range(n)]


def _fx_dano():
    n = int(0.3 * SR_FX)
    return [math.sin(2 * math.pi * (240 - 150 * (i / n)) * i / SR_FX) * math.exp(-8.0 * i / SR_FX) for i in range(n)]


FX = {'arbusto': _fx_arbusto, 'quebra': _fx_quebra, 'golpe': _fx_golpe, 'pegar': _fx_pegar, 'conquista': _fx_conquista,
      'toc': _fx_toc, 'dano': _fx_dano}


class Sfx:
    NIVEIS = {'desl': 0.0, 'baixa': 0.35, 'media': 0.65, 'alta': 1.0}

    def __init__(self):
        self.nivel = 'media'
        self.sons = {}
        self.pronto = {}
        self.carregador = None
        try:
            from kivy.core.audio import SoundLoader
            self.carregador = SoundLoader
        except Exception:
            pass
        threading.Thread(target=self._gerar, daemon=True).start()

    def _caminho(self, nome):
        base = caminho_cache()
        return os.path.join(os.path.dirname(base), '.jogo_samuel_fx_%s_v%d.wav' % (nome, VERSAO_SFX)) if base else None

    def _gerar(self):
        try:
            for nome, fn in FX.items():
                c = self._caminho(nome)
                if not c:
                    continue
                if not os.path.exists(c):
                    x = fn()
                    pico = max(0.001, max(abs(v) for v in x))
                    gravar_wav_fx(c, array.array('h', [int(v / pico * 0.85 * 32767) for v in x]))
                self.pronto[nome] = c
        except Exception:
            pass

    def tocar(self, nome, vol=1.0):
        v = self.NIVEIS.get(self.nivel, 0.65) * vol
        if v <= 0.0 or self.carregador is None or nome not in self.pronto:
            return
        try:
            s = self.sons.get(nome)
            if s is None:
                s = self.carregador.load(self.pronto[nome])
                self.sons[nome] = s
            if s is not None:
                s.volume = min(1.0, v)
                s.stop()
                s.play()
        except Exception:
            pass


def gravar_wav_fx(caminho, amostras):
    with wave.open(caminho + '.tmp', 'wb') as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(SR_FX)
        w.writeframes(amostras.tobytes())
    os.replace(caminho + '.tmp', caminho)


# ---------------- Geometria ----------------
# Face = (vértices, normal, cor já iluminada, nome da textura ou None, uvs ou None)
# Objeto = (cx, cy, cz, raio, faces, faces_longe ou None, usa_neblina)

def objeto(faces, neblina=True, longe=None):
    pts = [v for f in faces for v in f[0]]
    xs = [p[0] for p in pts]
    ys = [p[1] for p in pts]
    zs = [p[2] for p in pts]
    cx, cy, cz = (min(xs) + max(xs)) / 2, (min(ys) + max(ys)) / 2, (min(zs) + max(zs)) / 2
    raio = math.sqrt((max(xs) - min(xs)) ** 2 + (max(ys) - min(ys)) ** 2 + (max(zs) - min(zs)) ** 2) / 2
    return (cx, cy, cz, raio, faces, longe, neblina)


NEUTRAS = ('grama', 'terra', 'casca', 'folhas', 'rocha')


def neutra(cor, tex):
    """Texturas neutras escurecem a cor; compensa para o tom médio continuar igual ao da cor pedida."""
    if tex in NEUTRAS:
        m = MEDIAS[tex]
        return (min(1.0, cor[0] / m[0]), min(1.0, cor[1] / m[1]), min(1.0, cor[2] / m[2]))
    return cor


def _plano(P, A, B, N, cor, tex, esc, tile):
    cor = neutra(cor, tex)
    la = math.sqrt(dot(A, A))
    lb = math.sqrt(dot(B, B))
    if la < 1e-6 or lb < 1e-6:
        return []
    ah = (A[0] / la, A[1] / la, A[2] / la)
    bh = (B[0] / lb, B[1] / lb, B[2] / lb)
    nu = max(1, int(math.ceil(la / tile - 1e-6))) if tex else 1
    nv = max(1, int(math.ceil(lb / tile - 1e-6))) if tex else 1
    lit = sombrear(cor, N)
    faces = []
    for i in range(nu):
        for j in range(nv):
            u0, u1, v0, v1 = i / nu, (i + 1) / nu, j / nv, (j + 1) / nv
            verts = [(P[0] + A[0] * u + B[0] * v, P[1] + A[1] * u + B[1] * v, P[2] + A[2] * u + B[2] * v)
                     for u, v in ((u0, v0), (u1, v0), (u1, v1), (u0, v1))]
            uvs = [(dot(p, ah) / esc, dot(p, bh) / esc) for p in verts] if tex else None
            faces.append((verts, N, lit, tex, uvs))
    return faces


def caixa(x0, x1, y0, y1, z0, z1, cor, tex=None, esc=2.0, tile=2.0, so=None, cores=None, texs=None):
    cores = cores or {}
    texs = texs or {}
    dx, dy, dz = x1 - x0, y1 - y0, z1 - z0
    defs = {
        'topo': ((x0, y1, z0), (dx, 0, 0), (0, 0, dz), (0, 1, 0)),
        'base': ((x0, y0, z0), (dx, 0, 0), (0, 0, dz), (0, -1, 0)),
        'sul': ((x0, y0, z0), (dx, 0, 0), (0, dy, 0), (0, 0, -1)),
        'norte': ((x0, y0, z1), (dx, 0, 0), (0, dy, 0), (0, 0, 1)),
        'oeste': ((x0, y0, z0), (0, 0, dz), (0, dy, 0), (-1, 0, 0)),
        'leste': ((x1, y0, z0), (0, 0, dz), (0, dy, 0), (1, 0, 0)),
    }
    faces = []
    for nome in (so or tuple(defs)):
        P, A, B, N = defs[nome]
        if nome in cores:
            faces += _plano(P, A, B, N, cores[nome], None, esc, tile)
        else:
            faces += _plano(P, A, B, N, cor, texs.get(nome, tex), esc, tile)
    return faces


def _var(cor, rng, quanto):
    if not rng or quanto <= 0:
        return cor
    k = 1.0 + rng.uniform(-quanto, quanto)
    return (min(1, cor[0] * k), min(1, cor[1] * k), min(1, cor[2] * k))


def prisma_v(cx, cz, y0, y1, r0, r1, lados, cor, rng=None, var=0.0, tampa=True, tex=None, esc=1.0):
    """Cilindro / cone vertical (r1 = 0 vira cone). Com tex, ganha coordenadas de textura."""
    faces = []
    slope = (r0 - r1) / max(1e-6, (y1 - y0))
    cor = neutra(cor, tex)
    rm = (r0 + r1) / 2.0 if r1 >= 1e-6 else r0 * 0.6
    for i in range(lados):
        a0 = 2 * math.pi * i / lados
        a1 = 2 * math.pi * (i + 1) / lados
        am = (a0 + a1) / 2
        n = normalizar((math.cos(am), slope, math.sin(am)))
        p00 = (cx + r0 * math.cos(a0), y0, cz + r0 * math.sin(a0))
        p01 = (cx + r0 * math.cos(a1), y0, cz + r0 * math.sin(a1))
        u0, u1, vh = a0 * rm / esc, a1 * rm / esc, (y1 - y0) / esc
        if r1 < 1e-6:
            verts = [p00, p01, (cx, y1, cz)]
            uvs = [(u0, 0.0), (u1, 0.0), ((u0 + u1) / 2, vh)] if tex else None
        else:
            verts = [p00, p01, (cx + r1 * math.cos(a1), y1, cz + r1 * math.sin(a1)),
                     (cx + r1 * math.cos(a0), y1, cz + r1 * math.sin(a0))]
            uvs = [(u0, 0.0), (u1, 0.0), (u1, vh), (u0, vh)] if tex else None
        faces.append((verts, n, sombrear(_var(cor, rng, var), n), tex, uvs))
    if tampa and r1 >= 1e-6:
        topo = [(cx + r1 * math.cos(2 * math.pi * i / lados), y1, cz + r1 * math.sin(2 * math.pi * i / lados))
                for i in range(lados)]
        uvs = [(p[0] / esc, p[2] / esc) for p in topo] if tex else None
        faces.append((topo, (0, 1, 0), sombrear(cor, (0, 1, 0)), tex, uvs))
    return faces


def esfera(cx, cy, cz, r, lados, aneis, cor, sy=1.0, rng=None, var=0.0, jitter=0.0, tex=None, esc=1.0):
    """Esfera / elipsoide de poucos polígonos, iluminada de forma suave. Com tex, ganha UVs."""
    cor = neutra(cor, tex)

    def ponto(lat, lon):
        rr = r * (1.0 + (rng.uniform(-jitter, jitter) if (rng and jitter) else 0.0))
        return (cx + rr * math.cos(lat) * math.cos(lon), cy + rr * sy * math.sin(lat),
                cz + rr * math.cos(lat) * math.sin(lon))

    lats = [-math.pi / 2 + math.pi * (k + 1) / (aneis + 1) for k in range(aneis)]
    dl = 2 * math.pi / lados
    anel = [[ponto(lat, i * dl) for i in range(lados)] for lat in lats]
    fundo = (cx, cy - r * sy, cz)
    topo = (cx, cy + r * sy, cz)
    kk = r * 0.85 / esc
    vv = [(lat + math.pi / 2) * kk for lat in lats]
    v_f, v_t = 0.0, math.pi * kk
    caras = []
    for i in range(lados):
        j = (i + 1) % lados
        ui, uj = i * dl * kk, (i + 1) * dl * kk
        caras.append(([fundo, anel[0][j], anel[0][i]], [((ui + uj) / 2, v_f), (uj, vv[0]), (ui, vv[0])]))
        for k in range(aneis - 1):
            caras.append(([anel[k][i], anel[k][j], anel[k + 1][j], anel[k + 1][i]],
                          [(ui, vv[k]), (uj, vv[k]), (uj, vv[k + 1]), (ui, vv[k + 1])]))
        caras.append(([anel[-1][i], anel[-1][j], topo], [(ui, vv[-1]), (uj, vv[-1]), ((ui + uj) / 2, v_t)]))
    faces = []
    for verts, uv in caras:
        mx = sum(p[0] for p in verts) / len(verts)
        my = sum(p[1] for p in verts) / len(verts)
        mz = sum(p[2] for p in verts) / len(verts)
        n = normalizar((mx - cx, (my - cy) / (sy * sy), mz - cz))
        if n is None:
            continue
        faces.append((verts, n, sombrear(_var(cor, rng, var), n), tex, uv if tex else None))
    return faces


def reta(x0, z0, x1, z1, y, cor, tex=None, tile=4.0, esc=2.0):
    """Chão / teto plano retangular (normal para cima se for chão)."""
    return _plano((x0, y, z0), (x1 - x0, 0, 0), (0, 0, z1 - z0), (0, 1, 0), cor, tex, esc, tile)


def teto_plano(x0, z0, x1, z1, y, cor):
    """Teto interno: recebe luz ambiente clara (sem passar pelo sombreamento, que o deixaria cinza-escuro)."""
    fs = _plano((x0, y, z0), (x1 - x0, 0, 0), (0, 0, z1 - z0), (0, -1, 0), cor, None, 2.0, 99.0)
    return [(v, n, (cor[0] * 0.86, cor[1] * 0.86, cor[2] * 0.86), t, uv) for (v, n, c, t, uv) in fs]


# ---------------- Natureza e objetos redondos ----------------
VERDES = [(0.22, 0.50, 0.24), (0.30, 0.56, 0.22), (0.20, 0.44, 0.28), (0.36, 0.58, 0.25), (0.42, 0.55, 0.20),
          (0.18, 0.42, 0.22), (0.48, 0.52, 0.22)]
TRONCO = (0.42, 0.30, 0.20)


def arvore(x, z, rng):
    escala = rng.uniform(0.75, 1.5)
    verde = rng.choice(VERDES)
    if rng.random() < 0.4:  # pinheiro
        verde = (0.14, 0.40, 0.24)
        f = prisma_v(x, z, 0, 2.2 * escala, 0.22 * escala, 0.14 * escala, 6, TRONCO, rng, 0.05, True, 'casca', 0.8)
        for k in range(3):
            y0 = (1.4 + k * 1.2) * escala
            f += prisma_v(x, z, y0, y0 + 1.9 * escala, (1.5 - k * 0.38) * escala, 0, 8, verde, rng, 0.08, True, 'folhas', 1.3)
        lod = prisma_v(x, z, 0, 2.2 * escala, 0.2 * escala, 0.15 * escala, 3, TRONCO, rng, 0, False)
        lod += prisma_v(x, z, 1.4 * escala, 5.2 * escala, 1.4 * escala, 0, 5, verde, rng, 0.05)
        alt = 5.4 * escala
    else:
        f = prisma_v(x, z, 0, 2.4 * escala, 0.24 * escala, 0.16 * escala, 6, TRONCO, rng, 0.05, True, 'casca', 0.8)
        f += esfera(x, 3.5 * escala, z, 1.65 * escala, 8, 2, verde, 0.92, rng, 0.07, 0.08, 'folhas', 1.3)
        lod = prisma_v(x, z, 0, 2.4 * escala, 0.2 * escala, 0.15 * escala, 3, TRONCO, rng, 0, False)
        lod += esfera(x, 3.5 * escala, z, 1.6 * escala, 5, 1, verde, 0.9, rng, 0.05)
        alt = 5.2 * escala
    return objeto(f, True, lod), (x, z, 0.30 * escala, 40.0)


def arbusto(x, z, rng):
    r = rng.uniform(0.55, 0.95)
    verde = rng.choice(VERDES)
    f = esfera(x, r * 0.55, z, r, 7, 2, verde, 0.65, rng, 0.08, 0.06, 'folhas', 0.9)
    lod = esfera(x, r * 0.55, z, r, 5, 1, verde, 0.65, rng, 0.05)
    return objeto(f, True, lod), (x, z, r * 0.85, 0.001)  # h=0.001: sem colisão, só farfalhar


def pedra_pequena(x, z, rng):
    r = rng.uniform(0.35, 0.8)
    cinza = rng.choice([(0.55, 0.55, 0.57), (0.50, 0.50, 0.52), (0.60, 0.58, 0.55)])
    f = esfera(x, r * 0.4, z, r, 6, 2, cinza, 0.6, rng, 0.08, 0.18, 'rocha', 1.1)
    lod = esfera(x, r * 0.4, z, r, 5, 1, cinza, 0.6, rng, 0.05, 0.1)
    return objeto(f, True, lod), (x, z, r * 0.9, r * 0.8)


def pedra_grande(x, z, rng, h=1.5):
    cinza = (0.56, 0.55, 0.57)
    f = prisma_v(x, z, 0, h, 1.9, 1.45, 8, cinza, rng, 0.08, True, 'rocha', 1.8)
    f += esfera(x, h - 0.05, z, 1.45, 8, 1, cinza, 0.10, rng, 0.06, 0.03, 'rocha', 1.8)
    lod = prisma_v(x, z, 0, h, 1.8, 1.4, 5, cinza, rng, 0.05)
    return objeto(f, True, lod), (x, z, 1.75, h)


def flor(x, z, rng):
    cor = rng.choice([(0.95, 0.85, 0.30), (0.96, 0.96, 0.92), (0.90, 0.50, 0.70), (0.65, 0.55, 0.92)])
    f = prisma_v(x, z, 0.0, 0.28, 0.02, 0.02, 3, (0.25, 0.55, 0.25), None, 0, False)
    f += esfera(x, 0.32, z, 0.13, 5, 1, cor, 0.7)
    return objeto(f, True, None)


def tufo(x, z, rng):
    """Moita de capim: 3 a 5 folhas finas em cone."""
    f = []
    base = rng.choice([(0.30, 0.58, 0.24), (0.36, 0.62, 0.26), (0.26, 0.52, 0.22)])
    for k in range(rng.randint(3, 5)):
        ox, oz = rng.uniform(-0.12, 0.12), rng.uniform(-0.12, 0.12)
        h = rng.uniform(0.28, 0.55)
        f += prisma_v(x + ox, z + oz, 0.0, h, 0.045, 0.0, 3, base, rng, 0.06, False)
    return objeto(f, True, None)


def barril(x, z, rng, cor=(0.36, 0.42, 0.46), h=1.0):
    f = prisma_v(x, z, 0, h, 0.44, 0.44, 10, cor, rng, 0.05)
    f += prisma_v(x, z, h * 0.3, h * 0.36, 0.455, 0.455, 10, (0.2, 0.2, 0.22), None, 0, False)
    f += prisma_v(x, z, h * 0.66, h * 0.72, 0.455, 0.455, 10, (0.2, 0.2, 0.22), None, 0, False)
    return objeto(f, False, None), (x, z, 0.46, h)


def coluna(x, z, h, tex_cor=(0.62, 0.62, 0.64)):
    f = prisma_v(x, z, 0, h, 0.42, 0.42, 10, tex_cor)
    f += prisma_v(x, z, 0, 0.25, 0.55, 0.55, 10, (0.5, 0.5, 0.52))
    f += prisma_v(x, z, h - 0.25, h, 0.55, 0.55, 10, (0.5, 0.5, 0.52))
    return objeto(f, False, None), (x, z, 0.55, h)


# ---------------- Construção dos mapas ----------------
class Construtor:
    def __init__(self):
        self.fundo = []    # desenhado primeiro, sem ordenar (chão, pisos, tetos)
        self.objs = []     # desenhado depois, do mais longe para o mais perto
        self.caixas = []   # (x0, x1, z0, z1, y0, y1)
        self.circ = []     # (cx, cz, raio, altura)
        self.tetos = []    # (x0, x1, z0, z1, y)
        self.gemas = []    # [x, y, z, ativa, altura do chão embaixo]

    def fundo_faces(self, faces, neblina=False):
        for f in faces:
            self.fundo.append(objeto([f], neblina))

    def caixa(self, x0, x1, y0, y1, z0, z1, cor, tex=None, esc=2.0, colide=True, so=None, cores=None, texs=None):
        self.objs.append(objeto(caixa(x0, x1, y0, y1, z0, z1, cor, tex, esc, 2.0, so, cores, texs), False))
        if colide:
            self.caixas.append((x0, x1, z0, z1, y0, y1))

    def coloca(self, par):
        ob, circ = par
        self.objs.append(ob)
        if circ:
            self.circ.append(circ)

    def gema(self, x, z, chao=0.0):
        self.gemas.append([x, chao + 0.9, z, True, chao])


def parede(b, eixo, pos, a0, a1, H, vaos, cor, tex_int, tex_ext, ext, esp=0.3):
    """Parede ao longo de 'x' (z = pos) ou de 'z' (x = pos), com vãos [(ini, fim, y0, y1)] (portas e janelas)."""
    partes = []
    cursor = a0
    for (i, f, y0, y1) in sorted(vaos):
        if i > cursor:
            partes.append((cursor, i, 0, H))
        if y0 > 0:
            partes.append((i, f, 0, y0))
        if y1 < H:
            partes.append((i, f, y1, H))
        cursor = f
    if cursor < a1:
        partes.append((cursor, a1, 0, H))
    h = esp / 2.0
    for (i, f, y0, y1) in partes:
        n = max(1, int(math.ceil((f - i) / 4.0)))
        for k in range(n):
            s0 = i + (f - i) * k / n
            s1 = i + (f - i) * (k + 1) / n
            texs = {}
            if eixo == 'x':
                texs['sul'] = tex_ext if ext == 'sul' else tex_int
                texs['norte'] = tex_ext if ext == 'norte' else tex_int
                b.caixa(s0, s1, y0, y1, pos - h, pos + h, cor, tex_int, 2.0, True, None, None, texs)
            else:
                texs['oeste'] = tex_ext if ext == 'oeste' else tex_int
                texs['leste'] = tex_ext if ext == 'leste' else tex_int
                b.caixa(pos - h, pos + h, y0, y1, s0, s1, cor, tex_int, 2.0, True, None, None, texs)


def disco(cx, cz, y, r, lados, cor):
    pts = [(cx + r * math.cos(2 * math.pi * i / lados), y, cz + r * math.sin(2 * math.pi * i / lados))
           for i in range(lados)]
    return [(pts, (0, 1, 0), sombrear(cor, (0, 1, 0)), None, None)]


def livre(x, z, circs, folga):
    for (cx, cz, r, h) in circs:
        if (x - cx) ** 2 + (z - cz) ** 2 < (r + folga) ** 2:
            return False
    return True


def cor_grama(i, j):
    v = (math.sin(i * 1.3 + j * 0.7) + math.sin(j * 1.9 - i * 0.4)) * 0.028
    return (0.37 + v, 0.56 + v * 1.2, 0.28 + v * 0.5)


def chao_grama(b, x0, x1, z0, z1, passo, pular=None):
    nx = int(round((x1 - x0) / passo))
    nz = int(round((z1 - z0) / passo))
    for i in range(nx):
        for j in range(nz):
            ax, az = x0 + i * passo, z0 + j * passo
            if pular and pular(ax, az, ax + passo, az + passo):
                continue
            b.fundo_faces(reta(ax, az, ax + passo, az + passo, 0.0, cor_grama(i, j), 'grama', 9.0, 2.6), True)


def finalizar(b, nome, ceu, escuro, neblina, dist, inicio, limite):
    return {
        'nome': nome, 'ceu': ceu, 'escuro': escuro, 'neblina': neblina, 'dist': dist,
        'fundo': b.fundo, 'objs': b.objs, 'caixas': b.caixas, 'circ': b.circ, 'tetos': b.tetos,
        'gemas': b.gemas, 'inicio': inicio, 'limite': limite,
    }


def espalhar(b, rng, n, area, fabrica, folga, proibidos=()):
    x0, x1, z0, z1 = area
    feitos = 0
    tent = 0
    while feitos < n and tent < n * 40:
        tent += 1
        x, z = rng.uniform(x0, x1), rng.uniform(z0, z1)
        if not livre(x, z, b.circ, folga) or not livre(x, z, proibidos, 0.5):
            continue
        b.coloca(fabrica(x, z, rng))
        feitos += 1


# ======================= CAVERNA (entrada ao sul) =======================
def caverna(b, rng, cx, cz, gema_comum=True):
    W, D, H = 5.5, 5.0, 3.2
    x0, x1, z0, z1 = cx - W, cx + W, cz - D, cz + D
    ROC = (0.50, 0.49, 0.51)
    b.circ.append((cx, cz, 9.5, 0))          # reserva o espaço (sem colisão)
    b.fundo_faces(reta(x0, z0, x1, z1, 0.012, (0.66, 0.64, 0.66), 'pedra', 6.0, 2.2))
    P = lambda eixo, pos, a0, a1, vaos, ext: parede(b, eixo, pos, a0, a1, H, vaos, ROC, 'rocha', 'rocha', ext, 0.8)
    P('x', z1, x0, x1, [], 'norte')
    P('z', x0, z0, z1, [], 'oeste')
    P('z', x1, z0, z1, [], 'leste')
    P('x', z0, x0, x1, [(cx - 1.6, cx + 1.6, 0.0, 2.6)], 'sul')
    b.caixa(x0 - 0.9, x1 + 0.9, H, H + 1.2, z0 - 0.9, z1 + 0.9, ROC, 'rocha', 3.0)
    b.caixa(x0 + 0.8, x1 - 0.8, H + 1.2, H + 2.2, z0 + 0.8, z1 - 0.8, (0.45, 0.45, 0.47), 'rocha', 3.0)
    b.tetos.append((x0, x1, z0, z1, H))
    for sx in (-1, 1):
        b.coloca(pedra_grande(cx + sx * 4.9, z0 - 1.8, rng, 1.3))
    for (dx, dz, cor) in ((-4.4, 3.6, (0.45, 0.85, 1.0)), (4.5, 3.2, (0.70, 0.50, 1.0)), (-4.6, -1.5, (0.55, 0.90, 0.95)),
                          (4.4, -2.4, (0.95, 0.55, 0.85)), (-1.5, 4.3, (0.50, 0.80, 1.0)), (2.2, 4.4, (0.75, 0.55, 1.0))):
        f = prisma_v(cx + dx, cz + dz, 0, rng.uniform(0.6, 1.1), 0.20, 0.0, 5, cor, rng, 0.04, False)
        f += prisma_v(cx + dx + 0.25, cz + dz + 0.1, 0, rng.uniform(0.3, 0.6), 0.13, 0.0, 5, cor, rng, 0.04, False)
        b.objs.append(objeto(f, False, None))
    for sx in (-1, 1):                         # braseiros na entrada
        f = prisma_v(cx + sx * 2.2, z0 + 0.9, 0, 0.7, 0.12, 0.10, 5, (0.30, 0.22, 0.16), rng, 0.02, False)
        f += prisma_v(cx + sx * 2.2, z0 + 0.9, 0.7, 1.05, 0.16, 0.02, 5, (1.0, 0.62, 0.20), rng, 0.04, False)
        b.objs.append(objeto(f, False, None))
    for (dx, dz) in ((-3.6, 2.0), (3.6, -0.5), (-3.6, -2.6)):
        b.gemas.append([cx + dx, 0.9, cz + dz, True, 0.0, 'cristal'])
    if gema_comum:
        b.gema(cx, cz + 3.4, 0.0)


# ======================= MUNDO ABERTO =======================
def mapa_aberto():
    rng = random.Random(21)
    b = Construtor()
    TAM, LIM = 70.0, 60.0
    chao_grama(b, -TAM, TAM, -TAM, TAM, 7.0)
    inicio_livre = [(0, 0, 6.5, 0)]
    caverna(b, rng, -30.0, -14.0)
    caverna(b, rng, 27.0, 34.0)
    # pedras grandes (com gema em cima)
    topos = [(14, 22), (-24, 10), (30, -18), (-12, -34), (44, 28), (-42, -22)]
    for (x, z) in topos:
        b.coloca(pedra_grande(x, z, rng, 1.3))
        b.gema(x, z, 1.3)
    # floresta fechando o mundo além da barreira + árvores espalhadas dentro
    for _ in range(70):
        lado = rng.choice('nsle')
        t = rng.uniform(-TAM + 2, TAM - 2)
        d = rng.uniform(LIM + 2, TAM - 2)
        x, z = {'n': (t, d), 's': (t, -d), 'l': (d, t), 'e': (-d, t)}[lado]
        if livre(x, z, b.circ, 2.5):
            b.coloca(arvore(x, z, rng))
    espalhar(b, rng, 75, (-LIM, LIM, -LIM, LIM), arvore, 4.0, inicio_livre)
    espalhar(b, rng, 40, (-LIM, LIM, -LIM, LIM), arbusto, 2.2, inicio_livre)
    espalhar(b, rng, 24, (-LIM, LIM, -LIM, LIM), pedra_pequena, 2.5, inicio_livre)
    for _ in range(170):
        x, z = rng.uniform(-LIM, LIM), rng.uniform(-LIM, LIM)
        if livre(x, z, b.circ, 0.8):
            b.objs.append(tufo(x, z, rng))
    for _ in range(110):
        x, z = rng.uniform(-LIM, LIM), rng.uniform(-LIM, LIM)
        if livre(x, z, b.circ, 0.8):
            b.objs.append(flor(x, z, rng))
    # gemas no chão
    tent = 0
    while sum(1 for g in b.gemas if len(g) < 6) < 16 and tent < 2000:
        tent += 1
        x, z = rng.uniform(-LIM + 4, LIM - 4), rng.uniform(-LIM + 4, LIM - 4)
        if math.hypot(x, z) < 9 or not livre(x, z, b.circ, 2.2):
            continue
        if all(math.hypot(x - g[0], z - g[2]) > 12 for g in b.gemas):
            b.gema(x, z, 0.0)
    return finalizar(b, 'Mundo aberto', True, False, True, 74.0, (0.0, 0.0, 0.0), (-LIM, LIM, -LIM, LIM))


# ======================= CASA + QUINTAL =======================
def mapa_casa():
    rng = random.Random(5)
    b = Construtor()
    TAM, LIM = 36.0, 26.0
    H = 3.0
    dentro = lambda x0, z0, x1, z1: x1 > -9.5 and x0 < 9.5 and z1 > -7.5 and z0 < 7.5
    chao_grama(b, -TAM, TAM, -TAM, TAM, 6.0)   # chão inteiro (inclusive embaixo da casa: sem buraco branco)
    # caminho de terra até a porta da frente e dos fundos
    b.fundo_faces(reta(3.3, 7.2, 5.3, 28.0, 0.012, (0.66, 0.54, 0.38), 'terra', 8.0, 2.2), True)
    b.fundo_faces(reta(-5.3, -26.0, -3.1, -7.2, 0.012, (0.66, 0.54, 0.38), 'terra', 8.0, 2.2), True)
    # pisos e teto
    b.fundo_faces(reta(-0.85, -6.85, 8.85, 6.85, 0.01, (1, 1, 1), 'madeira'))
    b.fundo_faces(reta(-8.85, 1.15, -1.15, 6.85, 0.01, (1, 1, 1), 'madeira'))
    b.fundo_faces(reta(-8.85, -6.85, -1.15, 0.85, 0.01, (1, 1, 1), 'ladrilho'))
    b.fundo_faces(teto_plano(-8.85, -6.85, 8.85, 6.85, H, (0.94, 0.92, 0.87)))
    # telhado: laje grossa com beiral, visível por cima, por fora e por baixo do beiral
    b.fundo_faces(caixa(-9.7, 9.7, H, H + 0.30, -7.7, 7.7, (1.0, 1.0, 1.0), None, 2.0, 99.0, None,
                        {'base': (0.94, 0.92, 0.87), 'sul': (0.55, 0.38, 0.30), 'norte': (0.55, 0.38, 0.30),
                         'leste': (0.55, 0.38, 0.30), 'oeste': (0.55, 0.38, 0.30)}, {'topo': 'telhas'}))
    b.tetos.append((-9.0, 9.0, -7.0, 7.0, H))
    # paredes externas (tijolo por fora, reboco por dentro)
    P = lambda eixo, pos, a0, a1, vaos, ext: parede(b, eixo, pos, a0, a1, H, vaos, (1, 1, 1), 'reboco', 'tijolo', ext)
    janela = lambda i, f: (i, f, 1.0, 2.1)
    porta = lambda i, f: (i, f, 0.0, 2.3)
    P('x', -7.0, -9.15, 9.15, [porta(-5.0, -3.4), janela(6.0, 8.0)], 'sul')
    P('x', 7.0, -9.15, 9.15, [janela(-7.5, -5.0), janela(0.5, 2.5), porta(3.5, 5.1)], 'norte')
    P('z', -9.0, -7.0, 7.0, [janela(-5.0, -2.5), janela(3.0, 5.5)], 'oeste')
    P('z', 9.0, -7.0, 7.0, [janela(-4.5, -2.5), janela(3.0, 5.0)], 'leste')
    for (eixo, pos, i0, f0) in (('x', -7.0, 6.0, 8.0), ('x', 7.0, -7.5, -5.0), ('x', 7.0, 0.5, 2.5), ('z', -9.0, -5.0, -2.5),
                                ('z', -9.0, 3.0, 5.5), ('z', 9.0, -4.5, -2.5), ('z', 9.0, 3.0, 5.0)):
        moldura(b, eixo, pos, i0, f0, 1.0, 2.1)
    # paredes internas
    P('z', -1.0, -7.0, 7.0, [porta(-3.5, -2.0), porta(3.5, 5.0)], None)
    P('x', 1.0, -9.0, -1.0, [], None)
    # telhado (a parte de baixo é o teto, desenhado à parte)
    b.objs.append(objeto(caixa(-9.7, 9.7, H, H + 0.4, -7.7, 7.7, (0.64, 0.38, 0.32),
                               so=('topo', 'sul', 'norte', 'oeste', 'leste')), False))
    # ----- sala -----
    b.fundo_faces(disco(3.5, -1.0, 0.025, 2.6, 16, (0.70, 0.55, 0.45)))
    b.caixa(0.4, 4.8, 0.0, 0.5, -6.6, -5.0, (0.46, 0.52, 0.62))          # sofá
    b.caixa(0.4, 4.8, 0.5, 1.15, -6.6, -6.1, (0.42, 0.48, 0.58))
    b.caixa(0.4, 0.85, 0.5, 0.9, -6.1, -5.0, (0.42, 0.48, 0.58))
    b.caixa(4.35, 4.8, 0.5, 0.9, -6.1, -5.0, (0.42, 0.48, 0.58))
    b.caixa(8.2, 8.8, 0.0, 0.5, -1.2, 1.0, (0.45, 0.32, 0.22))           # móvel da TV
    b.caixa(8.55, 8.65, 0.8, 1.5, -0.9, 0.7, (0.08, 0.08, 0.1), colide=False)
    b.caixa(6.0, 8.5, 0.0, 1.4, 6.35, 6.8, (0.50, 0.36, 0.24))           # estante
    f = prisma_v(2.6, -2.8, 0.0, 0.45, 0.72, 0.72, 14, (0.55, 0.40, 0.28))
    b.objs.append(objeto(f, False))
    b.circ.append((2.6, -2.8, 0.72, 0.45))                                 # mesa de centro redonda
    f = prisma_v(7.8, -6.2, 0.0, 0.4, 0.26, 0.22, 8, (0.62, 0.40, 0.30))   # vaso e planta
    f += esfera(7.8, 1.0, -6.2, 0.55, 8, 2, (0.24, 0.55, 0.28), 1.0, rng, 0.06, 0.06)
    b.objs.append(objeto(f, False))
    b.circ.append((7.8, -6.2, 0.5, 1.6))
    f = prisma_v(5.8, -5.8, 0.0, 1.5, 0.05, 0.05, 6, (0.35, 0.33, 0.30))   # abajur de chão
    f += esfera(5.8, 1.65, -5.8, 0.24, 8, 2, (1.0, 0.90, 0.65))
    b.objs.append(objeto(f, False))
    # ----- cozinha -----
    b.caixa(-8.85, -7.95, 0.0, 0.95, -6.5, 0.2, (0.92, 0.92, 0.9), cores={'topo': (0.55, 0.55, 0.56)})
    b.caixa(-3.0, -1.5, 0.0, 1.5, 0.0, 0.8, (0.93, 0.94, 0.95))          # geladeira
    f = prisma_v(-4.5, -2.5, 0.0, 0.8, 0.9, 0.9, 14, (0.60, 0.44, 0.30))
    b.objs.append(objeto(f, False))
    b.circ.append((-4.5, -2.5, 0.9, 0.8))                                  # mesa redonda
    for (sx, sz) in ((-4.5, -4.0), (-4.5, -1.0), (-6.0, -2.5), (-3.0, -2.5)):
        b.caixa(sx - 0.22, sx + 0.22, 0.0, 0.5, sz - 0.22, sz + 0.22, (0.50, 0.36, 0.26))
    # ----- quarto -----
    b.caixa(-4.8, -2.6, 0.0, 0.45, 3.8, 6.7, (0.48, 0.34, 0.24))         # cama
    b.caixa(-4.7, -2.7, 0.45, 0.78, 3.9, 6.65, (0.93, 0.90, 0.84))
    b.caixa(-4.7, -2.7, 0.78, 0.86, 3.9, 5.3, (0.36, 0.55, 0.55))
    b.objs.append(objeto(esfera(-3.7, 0.95, 6.2, 0.38, 8, 2, (0.95, 0.94, 0.9), 0.45), False))
    b.caixa(-8.85, -7.8, 0.0, 1.6, 1.4, 3.0, (0.50, 0.36, 0.24))         # armário
    b.caixa(-2.1, -1.6, 0.0, 0.5, 5.8, 6.5, (0.50, 0.36, 0.24))          # criado-mudo
    b.objs.append(objeto(esfera(-1.85, 0.72, 6.15, 0.2, 8, 2, (1.0, 0.9, 0.65)), False))
    # ----- quintal -----
    inicio_ocup = [(4.3, 16.0, 2, 0), (-4.2, -15.0, 2, 0)]
    b.coloca(pedra_grande(13, -9, rng, 1.3))
    # mesa de jardim redonda com guarda-sol
    gx, gz = -12.0, -14.0
    f = prisma_v(gx, gz, 0.0, 0.75, 0.9, 0.9, 12, (0.78, 0.74, 0.66))
    f += prisma_v(gx, gz, 0.0, 0.7, 0.12, 0.12, 6, (0.4, 0.4, 0.4), None, 0, False)
    f += prisma_v(gx, gz, 1.9, 2.5, 1.7, 0.0, 10, (0.86, 0.80, 0.62))
    b.objs.append(objeto(f, True))
    b.circ.append((gx, gz, 0.9, 0.75))
    espalhar(b, rng, 26, (-LIM, LIM, -LIM, LIM), arvore, 4.5, [(0, 0, 11.5, 0), (4.3, 16.0, 2, 0), (-4.2, -15.0, 2, 0)])
    for _ in range(40):
        lado = rng.choice('nsle')
        t = rng.uniform(-TAM + 2, TAM - 2)
        d = rng.uniform(LIM + 1.5, TAM - 2)
        x, z = {'n': (t, d), 's': (t, -d), 'l': (d, t), 'e': (-d, t)}[lado]
        if livre(x, z, b.circ, 2.5):
            b.coloca(arvore(x, z, rng))
    espalhar(b, rng, 26, (-LIM, LIM, -LIM, LIM), arbusto, 2.2, [(0, 0, 11.0, 0)])
    espalhar(b, rng, 10, (-LIM, LIM, -LIM, LIM), pedra_pequena, 2.5, [(0, 0, 11.0, 0)])
    for _ in range(90):
        x, z = rng.uniform(-LIM, LIM), rng.uniform(-LIM, LIM)
        if max(abs(x) - 9.6, abs(z) - 7.6) > 0.5 and livre(x, z, b.circ, 0.8):
            b.objs.append(tufo(x, z, rng))
    for _ in range(90):
        x, z = rng.uniform(-LIM, LIM), rng.uniform(-LIM, LIM)
        if (not (-10 < x < 10 and -8 < z < 8)) and livre(x, z, b.circ, 0.8):
            b.objs.append(flor(x, z, rng))
    # ----- gemas -----
    b.gema(3.5, -0.6, 0.0)          # sala (tapete)
    b.gema(2.6, -5.8, 0.5)          # em cima do sofá
    b.gema(7.2, 6.55, 1.4)          # estante
    b.gema(-4.5, -2.5, 0.8)         # mesa da cozinha
    b.gema(-8.4, -3.0, 0.95)        # balcão
    b.gema(-3.7, 5.2, 0.86)         # cama
    b.gema(-8.3, 2.2, 1.6)          # armário
    b.gema(-6.0, 3.2, 0.0)          # quarto
    b.gema(-4.2, -12.0, 0.0)        # quintal dos fundos
    b.gema(gx, gz, 0.75)            # mesa do jardim
    b.gema(13.0, -9.0, 1.3)         # pedra do quintal
    b.gema(4.3, 18.0, 0.0)          # jardim da frente
    b.gema(-15.0, 14.0, 0.0)
    b.gema(19.0, 6.0, 0.0)
    return finalizar(b, 'Casa', True, False, True, 70.0, (4.3, -0.5, 0.0), (-LIM, LIM, -LIM, LIM))
# ======================= CASA FECHADA (casa com janelas, sem saída) =======================
def moldura(b, eixo, pos, i, f, y0, y1, esp=0.3):
    """Caixilho de janela (sem colisão): batentes, peitoril e, se a janela for larga, um montante no meio."""
    t, h = 0.09, esp / 2.0 + 0.08
    cor = (0.90, 0.88, 0.82)

    def bx(a0, a1, c0, c1):
        if eixo == 'x':
            b.caixa(a0, a1, c0, c1, pos - h, pos + h, cor, 'reboco', 2.0, False)
        else:
            b.caixa(pos - h, pos + h, c0, c1, a0, a1, cor, 'reboco', 2.0, False)
    bx(i, i + t, y0, y1)
    bx(f - t, f, y0, y1)
    bx(i, f, y0 - 0.04, y0 + t)
    bx(i, f, y1 - t, y1 + 0.04)
    if f - i > 1.9:
        m = (i + f) / 2.0
        bx(m - 0.035, m + 0.035, y0, y1)


def sofa(b, x0, x1, z0, z1, costas, cor):
    esc = tuple(c * 0.9 for c in cor)
    b.caixa(x0, x1, 0.0, 0.5, z0, z1, cor)
    dx, dz = x1 - x0, z1 - z0
    esp = 0.38
    if costas == 'oeste':
        b.caixa(x0, x0 + esp, 0.5, 1.1, z0, z1, esc)
        b.caixa(x0 + esp, x1, 0.5, 0.9, z0, z0 + 0.35, esc)
        b.caixa(x0 + esp, x1, 0.5, 0.9, z1 - 0.35, z1, esc)
    elif costas == 'leste':
        b.caixa(x1 - esp, x1, 0.5, 1.1, z0, z1, esc)
        b.caixa(x0, x1 - esp, 0.5, 0.9, z0, z0 + 0.35, esc)
        b.caixa(x0, x1 - esp, 0.5, 0.9, z1 - 0.35, z1, esc)
    elif costas == 'sul':
        b.caixa(x0, x1, 0.5, 1.1, z0, z0 + esp, esc)
        b.caixa(x0, x0 + 0.35, 0.5, 0.9, z0 + esp, z1, esc)
        b.caixa(x1 - 0.35, x1, 0.5, 0.9, z0 + esp, z1, esc)
    else:
        b.caixa(x0, x1, 0.5, 1.1, z1 - esp, z1, esc)
        b.caixa(x0, x0 + 0.35, 0.5, 0.9, z0, z1 - esp, esc)
        b.caixa(x1 - 0.35, x1, 0.5, 0.9, z0, z1 - esp, esc)


def cadeira(b, x, z, cor=(1.0, 0.88, 0.78), costas='sul'):
    b.caixa(x - 0.24, x + 0.24, 0.0, 0.48, z - 0.24, z + 0.24, cor, 'madeira')
    if costas == 'sul':
        b.caixa(x - 0.24, x + 0.24, 0.48, 1.0, z - 0.24, z - 0.18, cor, 'madeira', 2.0, False)
    elif costas == 'norte':
        b.caixa(x - 0.24, x + 0.24, 0.48, 1.0, z + 0.18, z + 0.24, cor, 'madeira', 2.0, False)
    elif costas == 'oeste':
        b.caixa(x - 0.24, x - 0.18, 0.48, 1.0, z - 0.24, z + 0.24, cor, 'madeira', 2.0, False)
    else:
        b.caixa(x + 0.18, x + 0.24, 0.48, 1.0, z - 0.24, z + 0.24, cor, 'madeira', 2.0, False)


def estante(b, x0, x1, z0, z1, h, frente, rng):
    """Estante de livros: corpo de madeira + lombadas coloridas na frente (sem colisão extra)."""
    b.caixa(x0, x1, 0.0, h, z0, z1, (1.0, 0.90, 0.80), 'madeira')
    cores = [(0.62, 0.22, 0.20), (0.22, 0.40, 0.58), (0.86, 0.72, 0.30), (0.28, 0.52, 0.34), (0.55, 0.40, 0.62), (0.90, 0.88, 0.80)]
    prat = [0.35 + k * 0.5 for k in range(int((h - 0.3) / 0.5))]
    for y in prat:
        if frente in ('sul', 'norte'):
            x = x0 + 0.1
            while x < x1 - 0.15:
                w = rng.uniform(0.05, 0.12)
                hh = rng.uniform(0.28, 0.42)
                zz = (z0 - 0.04, z0) if frente == 'sul' else (z1, z1 + 0.04)
                b.caixa(x, x + w, y, y + hh, zz[0], zz[1], rng.choice(cores), None, 2.0, False)
                x += w + 0.01
        else:
            z = z0 + 0.1
            while z < z1 - 0.15:
                w = rng.uniform(0.05, 0.12)
                hh = rng.uniform(0.28, 0.42)
                xx = (x0 - 0.04, x0) if frente == 'oeste' else (x1, x1 + 0.04)
                b.caixa(xx[0], xx[1], y, y + hh, z, z + w, rng.choice(cores), None, 2.0, False)
                z += w + 0.01


def vaso_planta(b, x, z, rng, escala=1.0):
    f = prisma_v(x, z, 0.0, 0.42 * escala, 0.26 * escala, 0.21 * escala, 8, (0.66, 0.42, 0.32))
    f += esfera(x, 0.95 * escala, z, 0.52 * escala, 8, 2, (0.24, 0.55, 0.28), 1.1, rng, 0.07, 0.07, 'folhas', 0.9)
    b.objs.append(objeto(f, False))
    b.circ.append((x, z, 0.4 * escala, 1.6))


def mapa_casa_fechada():
    rng = random.Random(11)
    b = Construtor()
    TAM, LIM = 52.0, 42.0
    H = 3.2
    chao_grama(b, -TAM, TAM, -TAM, TAM, 6.0)
    b.fundo_faces(reta(-1.2, -26.0, 1.2, -8.2, 0.012, (0.66, 0.54, 0.38), 'terra', 8.0, 2.2), True)   # caminho até a porta (trancada)
    # pisos e teto
    b.fundo_faces(reta(-9.9, -7.9, 9.9, 7.9, 0.01, (1, 1, 1), 'madeira'))
    b.fundo_faces(reta(-9.9, -7.9, -2.1, 0.9, 0.02, (1, 1, 1), 'ladrilho'))     # cozinha
    b.fundo_faces(teto_plano(-9.9, -7.9, 9.9, 7.9, H, (0.95, 0.93, 0.88)))
    b.fundo_faces(caixa(-10.8, 10.8, H, H + 0.30, -8.8, 8.8, (1.0, 1.0, 1.0), None, 2.0, 99.0, None,
                        {'base': (0.94, 0.92, 0.87), 'sul': (0.55, 0.38, 0.30), 'norte': (0.55, 0.38, 0.30),
                         'leste': (0.55, 0.38, 0.30), 'oeste': (0.55, 0.38, 0.30)}, {'topo': 'telhas'}))
    b.tetos.append((-10.0, 10.0, -8.0, 8.0, H))
    P = lambda eixo, pos, a0, a1, vaos, ext: parede(b, eixo, pos, a0, a1, H, vaos, (1, 1, 1), 'reboco', 'pedra', ext)
    jan = lambda i, f: (i, f, 0.95, 2.25)
    porta = lambda i, f: (i, f, 0.0, 2.3)
    fr = [jan(-8.5, -6.0), jan(-5.0, -3.0), jan(2.0, 4.2), jan(5.2, 7.4), jan(8.0, 9.5)]
    fu = [jan(-8.5, -6.0), jan(-5.0, -3.0), jan(0.0, 2.5), jan(3.5, 6.0), jan(7.0, 9.2)]
    oe = [jan(-6.5, -4.0), jan(-3.0, -0.5), jan(2.5, 5.0), jan(5.8, 7.3)]
    le = [jan(-6.5, -4.0), jan(-2.0, 1.0), jan(3.0, 5.5), jan(6.0, 7.4)]
    P('x', -8.0, -10.15, 10.15, fr, 'sul')
    P('x', 8.0, -10.15, 10.15, fu, 'norte')
    P('z', -10.0, -8.0, 8.0, oe, 'oeste')
    P('z', 10.0, -8.0, 8.0, le, 'leste')
    for (eixo, pos, lista) in (('x', -8.0, fr), ('x', 8.0, fu), ('z', -10.0, oe), ('z', 10.0, le)):
        for (i, f, y0, y1) in lista:
            moldura(b, eixo, pos, i, f, y0, y1)
    # porta da frente: fechada e trancada (parte da parede, com maçaneta)
    b.caixa(-0.95, 0.95, 0.0, 2.3, -8.15, -7.85, (1.0, 0.90, 0.80), 'madeira')
    b.caixa(-0.95, 0.95, 0.0, 2.3, -7.85, -7.80, (1.0, 0.90, 0.80), 'madeira', 2.0, False)
    b.objs.append(objeto(esfera(0.55, 1.1, -8.22, 0.07, 6, 1, (0.95, 0.80, 0.35)), False))
    # paredes internas
    P('z', -2.0, -8.0, 8.0, [porta(-5.5, -3.9), porta(3.0, 4.6)], None)
    P('x', 1.0, -10.0, -2.0, [porta(-8.0, -6.4)], None)
    # vigas do teto
    for vx in (-6.0, -2.0, 2.0, 6.0):
        b.caixa(vx - 0.15, vx + 0.15, H - 0.22, H, -7.85, 7.85, (0.9, 0.78, 0.68), 'madeira', 2.0, False)
    # ----- sala: lareira, sofás, mesa de centro, tapete -----
    b.fundo_faces(disco(4.8, -1.0, 0.03, 2.9, 20, (0.72, 0.30, 0.26)))
    b.fundo_faces(disco(4.8, -1.0, 0.035, 2.4, 20, (0.88, 0.80, 0.62)))
    b.fundo_faces(disco(4.8, -1.0, 0.04, 1.5, 20, (0.55, 0.30, 0.28)))
    b.caixa(-1.85, -0.95, 0.0, 1.35, -1.4, 1.4, (1.0, 1.0, 1.0), 'pedra')      # lareira
    b.caixa(-1.85, -1.25, 1.35, H, -0.7, 0.7, (1.0, 1.0, 1.0), 'pedra')       # chaminé
    b.caixa(-1.95, -1.0, 1.35, 1.42, -1.55, 1.55, (0.9, 0.78, 0.68), 'madeira', 2.0, False)   # prateleira da lareira
    b.caixa(-1.4, -1.2, 0.1, 0.75, -0.75, 0.75, (1.0, 0.55, 0.15), None, 2.0, False)           # brasas
    b.caixa(-1.4, -1.2, 0.5, 1.05, -0.35, 0.35, (1.0, 0.82, 0.30), None, 2.0, False)
    sofa(b, 6.9, 8.9, -3.9, -0.3, 'leste', (0.46, 0.52, 0.62))
    sofa(b, 2.6, 5.4, -5.7, -4.6, 'sul', (0.52, 0.44, 0.40))
    sofa(b, 2.6, 5.4, 2.6, 3.7, 'norte', (0.52, 0.44, 0.40))
    b.caixa(3.5, 5.3, 0.0, 0.42, -1.7, -0.4, (1.0, 0.90, 0.82), 'madeira')       # mesa de centro
    b.objs.append(objeto(esfera(4.4, 0.55, -1.05, 0.13, 6, 1, (0.9, 0.9, 0.85), 0.8), False))
    cadeira(b, 1.0, -2.8, (1.0, 0.82, 0.74), 'oeste')
    cadeira(b, 1.0, 0.6, (1.0, 0.82, 0.74), 'oeste')
    # ----- jantar -----
    b.caixa(3.0, 7.2, 0.0, 0.8, 5.0, 6.3, (1.0, 0.92, 0.84), 'madeira')
    for sx in (3.6, 5.1, 6.6):
        cadeira(b, sx, 4.45, costas='norte')
        cadeira(b, sx, 6.85, costas='sul')
    b.objs.append(objeto(prisma_v(5.1, 5.65, 2.3, 3.2, 0.015, 0.015, 4, (0.3, 0.3, 0.3), None, 0, False) +
                         esfera(5.1, 2.2, 5.65, 0.30, 8, 2, (1.0, 0.92, 0.70)), False))
    # ----- cama (canto) -----
    b.caixa(7.6, 9.8, 0.0, 0.45, 3.0, 7.6, (0.9, 0.78, 0.68), 'madeira', 2.0, False)
    b.caixa(7.7, 9.7, 0.45, 0.78, 3.1, 7.5, (0.93, 0.90, 0.84), None, 2.0, False)
    b.caixa(7.7, 9.7, 0.78, 0.86, 4.6, 7.5, (0.40, 0.55, 0.50), None, 2.0, False)
    b.caixa(7.7, 9.7, 0.78, 1.0, 3.1, 3.7, (0.96, 0.95, 0.92), None, 2.0, False)
    b.caixas.append((7.6, 9.8, 3.0, 7.6, 0.0, 0.78))                        # colisão da cama (um bloco só, dá para subir)
    # ----- cozinha -----
    b.caixa(-9.85, -8.95, 0.0, 0.95, -7.6, -1.0, (0.90, 0.90, 0.88), None, 2.0, True, None, {'topo': (0.55, 0.55, 0.57)})
    b.caixa(-7.4, -4.8, 0.0, 0.95, -4.5, -3.1, (0.88, 0.86, 0.80), None, 2.0, True, None, {'topo': (0.62, 0.42, 0.30)})   # ilha
    b.caixa(-3.4, -2.4, 0.0, 1.9, -7.6, -6.6, (0.92, 0.94, 0.95))                                                        # geladeira
    for sx in (-7.0, -6.1, -5.2):
        f = prisma_v(sx, -2.6, 0.0, 0.62, 0.2, 0.2, 8, (0.55, 0.38, 0.28))
        b.objs.append(objeto(f, False))
        b.circ.append((sx, -2.6, 0.2, 0.62))
    b.caixa(-7.0, -4.4, 0.0, 0.5, -0.2, 0.7, (0.9, 0.9, 0.88), None, 2.0, False)
    # ----- biblioteca -----
    estante(b, -9.4, -2.6, 1.2, 1.6, 2.5, 'norte', rng)
    estante(b, -9.8, -9.4, 2.0, 7.7, 2.4, 'leste', rng)
    b.caixa(-8.4, -5.8, 0.0, 0.78, 6.3, 7.5, (1.0, 0.90, 0.82), 'madeira')                 # escrivaninha
    cadeira(b, -7.1, 5.6, (0.30, 0.34, 0.30), 'norte')
    sofa(b, -5.2, -3.4, 3.2, 5.6, 'leste', (0.55, 0.30, 0.28))                              # poltrona de leitura
    b.fundo_faces(disco(-5.0, 4.0, 0.03, 1.7, 16, (0.34, 0.45, 0.42)))
    b.caixa(-4.2, -3.8, 0.0, 0.6, 6.8, 7.2, (0.45, 0.32, 0.22))
    b.objs.append(objeto(esfera(-4.0, 0.95, 7.0, 0.34, 10, 3, (0.30, 0.50, 0.62)), False))   # globo
    vaso_planta(b, -9.0, 7.2, rng, 1.1)
    vaso_planta(b, 9.2, 7.3, rng, 1.0)
    vaso_planta(b, 9.2, -7.2, rng, 1.2)
    vaso_planta(b, -2.7, -7.2, rng, 0.9)
    vaso_planta(b, 0.6, 7.2, rng, 1.0)
    # ----- lá fora: jardim, flores sob as janelas, floresta -----
    espalhar(b, rng, 34, (-LIM, LIM, -LIM, LIM), arvore, 4.5, [(0, 0, 14.0, 0)])
    for _ in range(30):
        lado = rng.choice('nsle')
        t = rng.uniform(-TAM + 2, TAM - 2)
        d = rng.uniform(LIM + 1.5, TAM - 2)
        x, z = {'n': (t, d), 's': (t, -d), 'l': (d, t), 'e': (-d, t)}[lado]
        if livre(x, z, b.circ, 2.5):
            b.coloca(arvore(x, z, rng))
    espalhar(b, rng, 30, (-LIM, LIM, -LIM, LIM), arbusto, 2.2, [(0, 0, 13.0, 0)])
    espalhar(b, rng, 12, (-LIM, LIM, -LIM, LIM), pedra_pequena, 2.5, [(0, 0, 13.0, 0)])
    for _ in range(190):
        x, z = rng.uniform(-30, 30), rng.uniform(-30, 30)
        fora = max(abs(x) - 10.6, abs(z) - 8.6)
        if fora > 0.3 and livre(x, z, b.circ, 0.8):
            b.objs.append(flor(x, z, rng) if rng.random() < 0.45 else tufo(x, z, rng))
    for k in range(10):                     # canteiros de flores junto das paredes
        x = rng.uniform(-9.5, 9.5)
        z = rng.choice((-9.2, 9.2))
        b.objs.append(flor(x, z, rng))
        b.objs.append(flor(x + 0.3, z + rng.uniform(-0.2, 0.2), rng))
    # ----- gemas (12) -----
    b.gema(7.9, -2.1, 0.5)          # sofá azul
    b.gema(4.4, -1.05, 0.42)        # mesa de centro
    b.gema(0.6, -1.0, 0.0)          # em frente à lareira
    b.gema(5.1, 5.65, 0.8)          # mesa de jantar
    b.gema(8.7, 5.2, 0.78)          # cama
    b.gema(-6.1, -3.8, 0.95)        # ilha da cozinha
    b.gema(-9.4, -4.0, 0.95)        # balcão
    b.gema(-7.1, 6.9, 0.78)         # escrivaninha
    b.gema(-4.3, 4.4, 0.5)          # poltrona
    b.gema(3.1, -8.0, 0.95)         # parapeito (frente)
    b.gema(1.2, 8.0, 0.95)          # parapeito (fundos)
    b.gema(10.0, -0.5, 0.95)        # parapeito (leste)
    return finalizar(b, 'Casa fechada', True, False, True, 70.0, (5.5, 0.5, 270.0), (-9.7, 9.7, -7.7, 7.7))


MAPAS = (('casa', mapa_casa), ('aberto', mapa_aberto), ('fechado', mapa_casa_fechada))
# ======================= MUNDOS CRIADOS PELO JOGADOR =======================
TIPOS_MUNDO = ['floresta', 'campo', 'vazio']
ROT_TIPOS = ['Floresta', 'Campo aberto', 'Terreno vazio']
DENS_MUNDO = [0.35, 1.0, 1.4]
ROT_DENS = ['Poucas', 'Normais', 'Muitas']
GEMAS_MUNDO = [0, 8, 16]
ROT_GEMAS = ['Nenhuma (livre)', '8 gemas', '16 gemas']
CHEATS = ()  # cheats agora são globais (aba Cheats nas configurações)
MAX_MUNDOS = 6
ITENS = (('gema', 'Gemas'), ('madeira', 'Madeira'), ('muda', 'Mudas'), ('pedra', 'Pedra'),
         ('cristal', 'Cristais'), ('tocha', 'Tocha'), ('machado', 'Machado'))


def inv_novo():
    return {k: 0 for k, _ in ITENS}


def arq_mundos():
    base = caminho_cache()
    return os.path.join(os.path.dirname(base), '.jogo_samuel_mundos.json') if base else None


def ler_mundos():
    try:
        with open(arq_mundos(), 'r') as f:
            dados = json.load(f)
        return [m for m in dados if isinstance(m, dict) and 'nome' in m][:MAX_MUNDOS]
    except Exception:
        return []


MUNDOS = ler_mundos()


def salvar_mundos():
    try:
        caminho = arq_mundos()
        with open(caminho + '.tmp', 'w') as f:
            json.dump(MUNDOS, f)
        os.replace(caminho + '.tmp', caminho)
    except Exception:
        pass


def novo_mundo(nome, tipo, dens, gemas, cheats):
    return {'nome': nome.strip() or 'Meu mundo', 'tipo': tipo, 'dens': dens, 'gemas': gemas,
            'cheats': dict(cheats), 'seed': random.randrange(1, 10 ** 6), 'plantadas': [], 'removidas': []}


def descricao_mundo(m):
    ts = ROT_TIPOS[TIPOS_MUNDO.index(m['tipo'])] if m['tipo'] in TIPOS_MUNDO else m['tipo']
    ativos = [r for k, r in CHEATS if m['cheats'].get(k)]
    return ts + (' • ' + ', '.join(ativos) if ativos else '')


def mapa_mundo(cfg):
    """Gera o mundo a partir da configuração salva; devolve o mapa com o registro das árvores editáveis."""
    rng = random.Random(cfg['seed'])
    b = Construtor()
    TAM, LIM = 70.0, 60.0
    chao_grama(b, -TAM, TAM, -TAM, TAM, 7.0)
    inicio_livre = [(0, 0, 6.5, 0)]
    reg = []                                     # [x, z, objeto, círculo de colisão]

    def fab_arvore(x, z, r):
        ob, circ = arvore(x, z, r)
        reg.append([x, z, ob, circ])
        return ob, circ

    tipo, mult = cfg['tipo'], cfg['dens']
    if tipo != 'vazio':
        caverna(b, rng, -30.0, -14.0, cfg['gemas'] > 0)
    if tipo != 'vazio':
        if tipo == 'floresta':
            for _ in range(int(70 * mult)):
                lado = rng.choice('nsle')
                t = rng.uniform(-TAM + 2, TAM - 2)
                d = rng.uniform(LIM + 2, TAM - 2)
                x, z = {'n': (t, d), 's': (t, -d), 'l': (d, t), 'e': (-d, t)}[lado]
                if livre(x, z, b.circ, 2.5):
                    b.coloca(fab_arvore(x, z, rng))
        n_arv = int((75 if tipo == 'floresta' else 14) * mult)
        espalhar(b, rng, n_arv, (-LIM, LIM, -LIM, LIM), fab_arvore, 4.0, inicio_livre)
        espalhar(b, rng, 30 if tipo == 'floresta' else 18, (-LIM, LIM, -LIM, LIM), arbusto, 2.2, inicio_livre)
        espalhar(b, rng, 20, (-LIM, LIM, -LIM, LIM), pedra_pequena, 2.5, inicio_livre)
        for _ in range(170 if tipo == 'floresta' else 260):
            x, z = rng.uniform(-LIM, LIM), rng.uniform(-LIM, LIM)
            if livre(x, z, b.circ, 0.8):
                b.objs.append(tufo(x, z, rng))
        for _ in range(110 if tipo == 'floresta' else 220):
            x, z = rng.uniform(-LIM, LIM), rng.uniform(-LIM, LIM)
            if livre(x, z, b.circ, 0.8):
                b.objs.append(flor(x, z, rng))
    tent = 0
    while sum(1 for g in b.gemas if len(g) < 6) < cfg['gemas'] and tent < 3000:
        tent += 1
        x, z = rng.uniform(-LIM + 4, LIM - 4), rng.uniform(-LIM + 4, LIM - 4)
        if math.hypot(x, z) < 9 or not livre(x, z, b.circ, 2.2):
            continue
        if all(math.hypot(x - g[0], z - g[2]) > 8 for g in b.gemas):
            b.gema(x, z, 0.0)
    mp = finalizar(b, cfg['nome'], True, False, True, 74.0, (0.0, 0.0, 0.0), (-LIM, LIM, -LIM, LIM))
    mp['arvores'] = reg
    # edições salvas: árvores cortadas e plantadas
    for (rx, rz) in cfg.get('removidas', []):
        for a in list(reg):
            if abs(a[0] - rx) < 0.05 and abs(a[1] - rz) < 0.05:
                tirar_arvore(mp, a)
    for (px_, pz_) in cfg.get('plantadas', []):
        por_arvore(mp, px_, pz_)
    return mp


def por_arvore(mp, x, z):
    r = random.Random(int(x * 100) * 7919 + int(z * 100))
    ob, circ = arvore(x, z, r)
    mp['objs'].append(ob)
    if circ:
        mp['circ'].append(circ)
    a = [x, z, ob, circ]
    mp['arvores'].append(a)
    return a


def tirar_arvore(mp, a):
    for lista, item in ((mp['objs'], a[2]), (mp['circ'], a[3]), (mp['arvores'], a)):
        for i, v in enumerate(lista):
            if v is item:
                del lista[i]
                break
# ======================= PERFIL DO PERSONAGEM (criado uma vez; editável em Configurações) =======================
PELES_TOM = ((0.96, 0.80, 0.68), (0.93, 0.74, 0.60), (0.80, 0.58, 0.42), (0.62, 0.43, 0.30), (0.42, 0.28, 0.20))
ROT_PELE = ['Clara', 'Bege', 'Morena', 'Marrom', 'Escura']
CABELO_COR = ((0.12, 0.09, 0.07), (0.30, 0.19, 0.10), (0.78, 0.60, 0.28), (0.60, 0.25, 0.12), (0.80, 0.80, 0.82), (0.36, 0.22, 0.60))
ROT_CABELO = ['Preto', 'Castanho', 'Loiro', 'Ruivo', 'Grisalho', 'Roxo']
ROUPA_COR = ((0.80, 0.66, 0.38), (0.36, 0.62, 0.44), (0.62, 0.40, 0.55), (0.45, 0.52, 0.60), (0.78, 0.36, 0.34), (0.92, 0.88, 0.80))
ROT_ROUPA = ['Mostarda', 'Verde', 'Lilás', 'Azul', 'Vermelho', 'Creme']
CALCA_COR = ((0.25, 0.28, 0.36), (0.40, 0.52, 0.70), (0.62, 0.55, 0.40), (0.14, 0.14, 0.16), (0.45, 0.20, 0.26))
ROT_CALCA = ['Jeans escuro', 'Jeans claro', 'Cáqui', 'Preta', 'Vinho']
OLHO_COR = ((0.22, 0.14, 0.08), (0.18, 0.36, 0.55), (0.20, 0.42, 0.26), (0.10, 0.08, 0.07))
ROT_OLHO = ['Castanhos', 'Azuis', 'Verdes', 'Pretos']
ESTILOS_CAB = {'m': ['Curto', 'Espetado'], 'f': ['Solto', 'Rabo de cavalo']}


def arq_perfil():
    base = caminho_cache()
    return os.path.join(os.path.dirname(base), '.jogo_samuel_perfil.json') if base else None


def perfil_padrao(sexo='m'):
    if sexo == 'f':
        return {'nome': 'Jogadora', 'sexo': 'f', 'pele': 1, 'cabelo': 1, 'estilo': 0, 'roupa': 2, 'calca': 1, 'olho': 0}
    return {'nome': 'Samuel', 'sexo': 'm', 'pele': 1, 'cabelo': 0, 'estilo': 0, 'roupa': 0, 'calca': 0, 'olho': 0}


def ler_perfil():
    try:
        with open(arq_perfil(), 'r') as f:
            p = json.load(f)
        base = perfil_padrao(p.get('sexo', 'm'))
        base.update({k: p[k] for k in base if k in p})
        return base
    except Exception:
        return None


PERFIL = ler_perfil()          # None = ainda não criou o personagem


def salvar_perfil(p):
    global PERFIL
    PERFIL = dict(p)
    try:
        caminho = arq_perfil()
        with open(caminho + '.tmp', 'w') as f:
            json.dump(PERFIL, f)
        os.replace(caminho + '.tmp', caminho)
    except Exception:
        pass


def perfil_para_rede(p):
    return [1 if p['sexo'] == 'f' else 0, p['pele'], p['cabelo'], p['estilo'], p['roupa'], p['calca'], p['olho']]


def perfil_de_rede(v):
    try:
        return {'sexo': 'f' if v[0] else 'm', 'pele': int(v[1]) % 5, 'cabelo': int(v[2]) % 6, 'estilo': int(v[3]) % 2,
                'roupa': int(v[4]) % 6, 'calca': int(v[5]) % 5, 'olho': int(v[6]) % 4}
    except Exception:
        return None


def atributos_perfil(p):
    """Perfil -> atributos lidos pelo desenho do personagem."""
    return dict(sexo=p['sexo'], pele=PELES_TOM[p['pele']], cab=CABELO_COR[p['cabelo']], estilo=p['estilo'],
                roupa=ROUPA_COR[p['roupa']], calca=CALCA_COR[p['calca']], olho=OLHO_COR[p['olho']])
# ======================= CONFIGURAÇÕES SALVAS (opções, idioma, cheats) =======================
CHEATS_G = (('voar', 'Voar'), ('pulo', 'Pulo alto'), ('fantasma', 'Atravessar paredes'), ('machado', 'Machado grátis'),
            ('plantar', 'Plantar árvores'), ('itens', 'Itens à vontade'), ('vida', 'Vida infinita'))


def arq_cfg():
    base = caminho_cache()
    return os.path.join(os.path.dirname(base), '.jogo_samuel_cfg.json') if base else None


def ler_cfg():
    base = {'idioma': 'pt-BR', 'cheats_ok': False, 'cheats': {}, 'opcoes': {}}
    try:
        with open(arq_cfg(), 'r') as f:
            d = json.load(f)
        for k in base:
            if k in d and isinstance(d[k], type(base[k])):
                base[k] = d[k]
    except Exception:
        pass
    return base


CONFIG = ler_cfg()


def salvar_cfg():
    try:
        caminho = arq_cfg()
        with open(caminho + '.tmp', 'w') as f:
            json.dump(CONFIG, f)
        os.replace(caminho + '.tmp', caminho)
    except Exception:
        pass

# ======================= REDE (celular <-> celular, sem servidor externo) =======================
PORTA = 8888
MAX_JOGADORES = 3
PORTA_AVISO = 8889


def ip_local():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(('10.255.255.255', 1))   # não envia nada: só descobre qual rede o celular usa
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        try:
            return socket.gethostbyname(socket.gethostname())
        except Exception:
            return '?'


class Rede:
    """Um celular cria a sala (anfitrião); os outros entram pelo IP (ou achando a sala sozinhos no mesmo Wi-Fi/hotspot)."""

    def __init__(self):
        self.modo = None
        self.status = 'Desconectado'
        self.meu_id = None
        self.remotos = {}
        self.conns = []
        self.lock = threading.Lock()
        self.rodando = False
        self.sock = None
        self.prox_id = 1

    # ---- anfitrião ----
    def criar(self):
        self.parar()
        srv = None
        erro = None
        for _ in range(5):
            try:
                srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                srv.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                srv.bind(('0.0.0.0', PORTA))
                srv.listen(4)
                srv.settimeout(1.0)
                erro = None
                break
            except Exception as e:
                erro = e
                time.sleep(0.4)
        if erro is not None:
            self.status = 'Erro ao criar a sala: %s' % erro
            return
        self.sock = srv
        self.rodando = True
        self.modo = 'host'
        self.meu_id = 0
        self.prox_id = 1
        self.status = 'Sala criada. Peça para o outro entrar com o IP: %s' % ip_local()
        threading.Thread(target=self._aceitar, args=(srv,), daemon=True).start()
        threading.Thread(target=self._avisar, daemon=True).start()

    def _aceitar(self, srv):
        while self.rodando and self.sock is srv:
            try:
                conn, addr = srv.accept()
            except socket.timeout:
                continue
            except Exception:
                break
            try:
                conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
                conn.settimeout(1.0)
            except Exception:
                pass
            with self.lock:
                cheio = len(self.conns) >= MAX_JOGADORES - 1
            if cheio:
                try:
                    conn.sendall(b'{"t":"cheio"}\n')
                    conn.close()
                except Exception:
                    pass
                continue
            cid = self.prox_id
            self.prox_id += 1
            with self.lock:
                self.conns.append((cid, conn))
            self._mandar(conn, {'t': 'hello', 'id': cid})
            self.status = 'Jogador conectado! (%d/%d)' % (len(self.conns) + 1, MAX_JOGADORES)
            threading.Thread(target=self._ler, args=(conn, cid), daemon=True).start()

    def _avisar(self):
        try:
            u = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            u.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
        except Exception:
            return
        while self.rodando and self.modo == 'host':
            try:
                u.sendto(b'SAMUEL', ('255.255.255.255', PORTA_AVISO))
            except Exception:
                pass
            time.sleep(1.0)
        try:
            u.close()
        except Exception:
            pass

    # ---- cliente ----
    def entrar(self, ip):
        self.parar()
        self.rodando = True
        self.modo = 'cliente'
        self.status = 'Procurando sala...' if not ip else 'Conectando a %s ...' % ip
        threading.Thread(target=self._entrar, args=(ip.strip(),), daemon=True).start()

    def _entrar(self, ip):
        if not ip:
            try:
                u = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                u.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                u.bind(('', PORTA_AVISO))
                u.settimeout(1.0)
                fim = time.time() + 8.0
                while self.rodando and time.time() < fim and not ip:
                    try:
                        dados, ende = u.recvfrom(64)
                        if dados.startswith(b'SAMUEL'):
                            ip = ende[0]
                    except socket.timeout:
                        pass
                u.close()
            except Exception:
                pass
            if not ip:
                if self.rodando:
                    self.status = 'Nenhuma sala encontrada. Digite o IP do anfitrião.'
                    self.rodando = False
                    self.modo = None
                return
        try:
            c = socket.create_connection((ip, PORTA), timeout=5.0)
            c.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
            c.settimeout(1.0)
        except Exception as e:
            self.status = 'Não consegui conectar (%s)' % e
            self.rodando = False
            self.modo = None
            return
        self.sock = c
        self.status = 'Conectado à sala de %s' % ip
        self._ler(c, None)

    # ---- comum ----
    def _mandar(self, conn, msg):
        try:
            conn.sendall((json.dumps(msg, separators=(',', ':')) + '\n').encode())
            return True
        except Exception:
            return False

    def _ler(self, conn, cid):
        buf = b''
        while self.rodando:
            try:
                dados = conn.recv(4096)
            except socket.timeout:
                continue
            except Exception:
                break
            if not dados:
                break
            buf += dados
            while b'\n' in buf:
                linha, buf = buf.split(b'\n', 1)
                try:
                    self._tratar(json.loads(linha.decode()), cid)
                except Exception:
                    pass
        # desconectou
        if self.modo == 'host':
            with self.lock:
                self.conns = [(i, c) for (i, c) in self.conns if c is not conn]
            self.remotos.pop(cid, None)
            self._espalhar({'t': 'bye', 'id': cid}, None)
            self.status = 'Jogador saiu. Aguardando... (%d/%d)' % (len(self.conns) + 1, MAX_JOGADORES)
        elif self.rodando and self.sock is conn:
            self.status = 'Desconectado da sala.'
            self.rodando = False
            self.modo = None
            self.remotos.clear()
        try:
            conn.close()
        except Exception:
            pass

    def _tratar(self, msg, cid):
        t = msg.get('t')
        if self.modo == 'host':
            if t == 's':
                msg['id'] = cid
                msg['T'] = time.time()
                self.remotos[cid] = msg
                self._espalhar(msg, cid)
        else:
            if t == 'cheio':
                self.status = 'Sala cheia (máximo %d jogadores).' % MAX_JOGADORES
                self.rodando = False
                self.modo = None
            elif t == 'hello':
                self.meu_id = msg['id']
            elif t == 's' and msg.get('id') != self.meu_id:
                msg['T'] = time.time()
                self.remotos[msg['id']] = msg
            elif t == 'bye':
                self.remotos.pop(msg.get('id'), None)

    def _espalhar(self, msg, menos):
        with self.lock:
            lista = list(self.conns)
        for (i, c) in lista:
            if i != menos:
                self._mandar(c, msg)

    def enviar(self, est):
        if not self.rodando or self.meu_id is None:
            return
        msg = dict(est)
        msg['t'] = 's'
        msg['id'] = self.meu_id
        if self.modo == 'host':
            self._espalhar(msg, None)
        elif self.sock is not None:
            self._mandar(self.sock, msg)

    def parar(self):
        self.rodando = False
        self.modo = None
        self.meu_id = None
        for (i, c) in list(self.conns):
            try:
                c.close()
            except Exception:
                pass
        self.conns = []
        if self.sock is not None:
            try:
                self.sock.shutdown(socket.SHUT_RDWR)   # acorda o accept() para liberar a porta já
            except Exception:
                pass
            try:
                self.sock.close()
            except Exception:
                pass
        self.sock = None
        self.remotos = {}
        self.status = 'Desconectado'

    def jogadores(self):
        agora = time.time()
        return {i: r for i, r in list(self.remotos.items()) if agora - r.get('T', 0) < 4.0}




# ======================= MOTOR 3D =======================
PUFFS = [(-1.1, -0.05, 0.55), (-0.55, 0.12, 0.75), (0.0, 0.22, 0.9), (0.6, 0.12, 0.75),
         (1.15, -0.05, 0.55), (0.0, -0.10, 0.8)]
CIRC12 = [(math.cos(2 * math.pi * k / 12), math.sin(2 * math.pi * k / 12)) for k in range(12)]


def anel_3d(p, d, r, lados):
    ref = (0.0, 0.0, 1.0) if abs(d[2]) < 0.9 else (1.0, 0.0, 0.0)
    u = normalizar(cross(d, ref))
    v = cross(d, u)
    return [(p[0] + r * (u[0] * math.cos(2 * math.pi * i / lados) + v[0] * math.sin(2 * math.pi * i / lados)),
             p[1] + r * (u[1] * math.cos(2 * math.pi * i / lados) + v[1] * math.sin(2 * math.pi * i / lados)),
             p[2] + r * (u[2] * math.cos(2 * math.pi * i / lados) + v[2] * math.sin(2 * math.pi * i / lados)))
            for i in range(lados)]


def prisma_livre(p0, p1, r0, r1, lados, cor, uv=False):
    """Cilindro entre dois pontos (usado nos braços). Devolve [(vértices, normal, cor)]."""
    d = normalizar(sub(p1, p0))
    a0 = anel_3d(p0, d, r0, lados)
    a1 = anel_3d(p1, d, r1, lados)
    faces = []
    for i in range(lados):
        j = (i + 1) % lados
        q = [a0[i], a0[j], a1[j], a1[i]]
        mx = sum(p[0] for p in q) / 4.0
        my = sum(p[1] for p in q) / 4.0
        mz = sum(p[2] for p in q) / 4.0
        t = dot(sub((mx, my, mz), p0), d)
        eixo = (p0[0] + d[0] * t, p0[1] + d[1] * t, p0[2] + d[2] * t)
        n = normalizar(sub((mx, my, mz), eixo))
        if n:
            if uv:
                K = max(1.0, 2.0 * math.pi * (r0 + r1) * 0.5 / 0.30)     # textura repete a cada ~30 cm
                Lv = max(0.3, math.sqrt(dot(sub(p1, p0), sub(p1, p0))) / 0.30)
                u0, u1 = K * i / lados, K * (i + 1) / lados
                faces.append((q, n, cor, [(u0, 0.0), (u1, 0.0), (u1, Lv), (u0, Lv)]))
            else:
                faces.append((q, n, cor))
    faces.append((list(a1), d, cor, None) if uv else (list(a1), d, cor))   # tampa
    return faces


INTRO_DUR = 4.2


def SAPATO_COR(e):
    return getattr(e, 'tenis', None) or (0.22, 0.20, 0.22)


class Cena(Widget):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.texs = {n: (None, MEDIAS[n]) for n, _ in GERADORES}   # começa só com cores; texturas entram quando prontas
        self._tex_pend = {}
        self._tex_todas = None
        self._tex_salvo = False
        cache = ler_cache()
        if cache:
            for n, (dados, media) in cache.items():
                self.texs[n] = (textura_gl(dados), media)
            self._tex_salvo = True
        else:
            threading.Thread(target=self._gerar_texturas, daemon=True).start()
        self.sens = SENS_PADRAO
        self.pausado = True
        self.cam_uid = None
        self.joy_uid = None
        self.joy_o = (0.0, 0.0)
        self.joy_k = (0.0, 0.0)
        self.joy_x = 0.0
        self.joy_y = 0.0
        self.hud = None
        self.ao_vencer = None
        self.ao_erro = None
        self.erro = None
        self.anim = 0.0
        self.qual = 1.0
        self.q_modo = 'auto'        # auto / baixa / media / alta
        self.dist_mult = 1.0
        self.texturas = True
        self.detalhe = 1            # 0 normal, 1 alto, 2 máximo (divisão das texturas)
        self.nuvens_on = True
        self.fps_on = False
        self.musica_nivel = 'baixa'
        self.sfx_nivel = 'media'
        self.correr = False
        self.t_arbusto = 0.0
        self.mundo = None
        self.cheats = {}
        self.inv = inv_novo()
        self.mao = None
        self.alt_alvo = 0.0
        self.corte = None            # árvore sendo cortada (animação)
        self.golpe = None            # fase do golpe do machado (0..1) ou None
        self.cena_on = True
        self.intro = False
        self.vitrine = False
        self.sexo, self.estilo = 'm', 0
        self.pele, self.cab, self.roupa, self.calca, self.olho = PELES_TOM[1], CABELO_COR[0], ROUPA_COR[0], CALCA_COR[0], OLHO_COR[0]
        if PERFIL:
            self.aplicar_perfil(PERFIL)
        self.intro_t = 0.0
        self.musica = Musica()
        self.sfx = Sfx()
        self.camera = 'primeira'    # primeira / terceira / segunda
        self.corpo_yaw = 0.0
        self.vig = None
        self.vig_falhou = False
        self.yaw_r = 0.0
        self.rede = Rede()
        self.t_rede = 0.0
        self.suaves = {}
        self.ult_pos = (0.0, 0.0)
        self.dt_med = 1.0 / 30.0
        self.n_quadros = 0
        self.cache = {}
        self.chave = None
        self.mapa = None
        self.px = self.pz = self.feet = self.vy = 0.0
        rng = random.Random(4)
        self.nuvens = [{'az': rng.uniform(0, 2 * math.pi), 'el': rng.uniform(0.10, 0.62),
                        's': rng.uniform(0.07, 0.15), 'v': rng.uniform(0.004, 0.010)} for _ in range(13)]
        self.carregar('casa')
        self.evento = Clock.schedule_interval(self.loop, 1.0 / 30.0)

    # ---------- Mapas ----------
    def _gerar_texturas(self):
        try:
            self._tex_todas = gerar_todas(lambda n, p: self._tex_pend.__setitem__(n, p))
        except Exception:
            self._tex_todas = {}

    def _tex_finalizar(self):
        """Chamado a cada quadro: cria (no thread principal) as texturas que a thread já terminou de gerar."""
        if self._tex_salvo:
            return
        for n in list(self._tex_pend.keys())[:2]:
            dados, media = self._tex_pend.pop(n)
            self.texs[n] = (textura_gl(dados), media)
        if self._tex_todas and not self._tex_pend:
            gravar_cache(self._tex_todas)
            self._tex_salvo = True

    def carregar(self, chave):
        if chave not in self.cache:
            fn = dict(MAPAS)[chave]
            self.cache[chave] = fn()
        self.chave = chave
        self.mundo = None
        self.cheats = {}
        self.inv = inv_novo()
        self.mao = None
        self.musica.trocar('campo' if chave == 'aberto' else 'casa')
        self.mapa = self.cache[chave]
        self.reiniciar()
        self.iniciar_intro()

    def carregar_mundo(self, cfg):
        self.mapa = mapa_mundo(cfg)
        self.chave = 'mundo'
        self.mundo = cfg
        self.cheats = dict(cfg.get('cheats', {}))
        self.inv = cfg.setdefault('inv', inv_novo())
        for k in inv_novo():
            self.inv.setdefault(k, 0)
        self.mao = None
        self.musica.trocar('campo')
        self.reiniciar()
        self.iniciar_intro()

    def aplicar_perfil(self, p):
        for k, v in atributos_perfil(p).items():
            setattr(self, k, v)

    def iniciar_intro(self):
        self.corte = None
        self.golpe = None
        self.intro = bool(self.cena_on)
        self.intro_t = 0.0

    def pular_intro(self):
        if self.intro:
            self.intro = False
            self.tempo = 0.0

    @property
    def machado(self):
        return self.mao == 'machado'

    @property
    def cheats(self):
        return CONFIG['cheats'] if CONFIG.get('cheats_ok') else {}

    @cheats.setter
    def cheats(self, v):
        pass

    def tem(self, k):
        return self.inv.get(k, 0) > 0 or (k == 'machado' and bool(self.cheats.get('machado')))

    def equipar(self, k):
        if self.mao == k:
            self.mao = None
        elif k in ('machado', 'tocha', 'gema', 'cristal', 'madeira', 'pedra', 'muda') and self.tem(k):
            self.mao = k

    def dar(self, k, n=1):
        self.inv[k] = self.inv.get(k, 0) + n
        if self.mundo is not None:
            salvar_mundos()

    # ---------- Edição de árvores (só nos mundos criados) ----------
    def plantar(self):
        if self.mundo is None or self.pausado or not self.cheats.get('plantar'):
            return
        mp = self.mapa
        yaw = math.radians(self.yaw)
        x, z = self.px + math.sin(yaw) * 3.5, self.pz + math.cos(yaw) * 3.5
        x, z = round(x, 2), round(z, 2)
        x0, x1, z0, z1 = mp['limite']
        if not (x0 < x < x1 and z0 < z < z1) or not livre(x, z, mp['circ'], 1.2):
            return
        por_arvore(mp, x, z)
        self.mundo['plantadas'].append([x, z])
        salvar_mundos()

    def cortar(self):
        if self.mundo is None or self.pausado or not self.cheats.get('machado'):
            return
        mp = self.mapa
        yaw = math.radians(self.yaw)
        fx, fz = math.sin(yaw), math.cos(yaw)
        melhor, md = None, 1e9
        for a in mp['arvores']:
            dx, dz = a[0] - self.px, a[1] - self.pz
            d = math.hypot(dx, dz)
            if d < 0.1 or d > 10.0 or (dx * fx + dz * fz) / d < 0.80:
                continue
            if d < md:
                melhor, md = a, d
        if melhor is None:
            return
        if self.corte is not None:
            return
        tirar_arvore(mp, melhor)       # sai da colisão e da lista; a queda é desenhada à parte
        ux, uz = melhor[0] - self.px, melhor[1] - self.pz
        dd = math.hypot(ux, uz) or 1.0
        self.mao = 'machado'
        self.corte = {'ob': melhor[2], 'x': melhor[0], 'z': melhor[1], 'ux': ux / dd, 'uz': uz / dd, 't': 0.0}
        par = [round(melhor[0], 2), round(melhor[1], 2)]
        pl = self.mundo['plantadas']
        for i, q in enumerate(pl):
            if abs(q[0] - melhor[0]) < 0.05 and abs(q[1] - melhor[1]) < 0.05:
                del pl[i]
                break
        else:
            self.mundo['removidas'].append([melhor[0], melhor[1]])
        salvar_mundos()

    def _corte_tick(self, dt):
        c = self.corte
        c['t'] += dt
        t = c['t']
        self.corpo_yaw = math.degrees(math.atan2(c['ux'], c['uz']))
        self.golpe = (t / 0.9) if t < 0.9 else None
        if t >= 2.3:
            self.inv['madeira'] += 3
            self.inv['muda'] += 1
            self.corte = None
            self.golpe = None
            if self.mundo is not None:
                salvar_mundos()

    def arvore_caindo(self):
        """Devolve a árvore em queda (objeto girado em torno da base) ou None."""
        c = self.corte
        if c is None:
            return None
        t = c['t']
        ang = 0.0
        for hit in (0.3, 0.6, 0.9):
            if hit <= t < hit + 0.6:
                dh = t - hit
                ang = math.radians(2.4 * math.exp(-9.0 * dh) * math.sin(42.0 * dh))
        if t > 0.9:
            ang += math.radians(82.0) * min(1.0, (t - 0.9) / 0.95) ** 2.2
        ux, uz, bx, bz = c['ux'], c['uz'], c['x'], c['z']
        ca, sa = math.cos(ang), math.sin(ang)

        def giro(p, rel):
            x, y, z = (p[0], p[1], p[2]) if not rel else p
            if not rel:
                x, z = x - bx, z - bz
            s = x * ux + z * uz
            lx, lz = x - s * ux, z - s * uz
            s2 = s * ca + y * sa
            y2 = y * ca - s * sa
            if rel:
                return (ux * s2 + lx, y2, uz * s2 + lz)
            return (bx + ux * s2 + lx, y2, bz + uz * s2 + lz)

        ob = c['ob']
        faces = [([giro(p, False) for p in f[0]], giro(f[1], True), f[2], f[3], f[4]) for f in ob[4]]
        cx, cy, cz = giro((ob[0], ob[1], ob[2]), False)
        return (cx, cy, cz, ob[3], faces, ob[5], ob[6])

    def subir(self, delta):
        if self.cheats.get('voar'):
            self.alt_alvo = max(0.0, min(60.0, self.alt_alvo + delta))

    def reiniciar(self):
        mp = self.mapa
        self.px, self.pz, self.yaw = mp['inicio']
        self.feet = 0.0
        self.vy = 0.0
        self.no_chao = True
        self.pitch = 0.0
        self.vel_f = self.vel_l = 0.0
        self.fase = 0.0
        self.bob_amp = 0.0
        self.tempo = 0.0
        self.venceu = False
        self.alt_alvo = 0.0
        self.soltar_controles()
        self.gemas = [g[:] for g in mp['gemas']]
        self.total = sum(1 for g in self.gemas if len(g) < 6)
        self.coletadas = 0

    def soltar_controles(self):
        self.cam_uid = None
        self.joy_uid = None
        self.joy_x = 0.0
        self.joy_y = 0.0

    # ---------- Toque: joystick (esquerda) e câmera (direita) ----------
    def joy_raio(self):
        return self.height * 0.16

    def _joy_atualizar(self, tx, ty):
        r = self.joy_raio()
        ox, oy = self.joy_o
        dx, dy = tx - ox, ty - oy
        d = math.hypot(dx, dy)
        if d > r:
            dx, dy = dx * r / d, dy * r / d
            d = r
        self.joy_k = (ox + dx, oy + dy)
        mag = d / r
        if mag < 0.12:
            self.joy_x = self.joy_y = 0.0
        else:
            forca = (mag - 0.12) / 0.88
            self.joy_x = dx / d * forca
            self.joy_y = dy / d * forca

    def on_touch_down(self, touch):
        if self.pausado:
            return False
        if self.intro:
            self.pular_intro()
            return True
        w, h = self.width, self.height
        if touch.x < w * 0.40:
            if self.joy_uid is None:
                r = self.joy_raio()
                self.joy_uid = touch.uid
                self.joy_o = (max(r * 1.1, touch.x), max(r * 1.1, min(touch.y, h - r * 1.1)))
                self._joy_atualizar(touch.x, touch.y)
            return True
        if self.cam_uid is None:
            self.cam_uid = touch.uid
            return True
        return False

    def on_touch_move(self, touch):
        if touch.uid == self.joy_uid:
            self._joy_atualizar(touch.x, touch.y)
            return True
        if touch.uid == self.cam_uid:
            self.yaw += touch.dx * self.sens
            self.pitch = max(-75.0, min(75.0, self.pitch + touch.dy * self.sens))
            return True
        return False

    def on_touch_up(self, touch):
        if touch.uid == self.joy_uid:
            self.joy_uid = None
            self.joy_x = self.joy_y = 0.0
            return True
        if touch.uid == self.cam_uid:
            self.cam_uid = None
            return True
        return False

    def pular(self):
        if self.pausado or self.venceu:
            return
        if self.cheats.get('voar'):
            self.subir(1.0)
        elif self.no_chao:
            self.vy = FORCA_PULO * (1.9 if self.cheats.get('pulo') else 1.0)
            self.no_chao = False

    # ---------- Física ----------
    def bloqueado(self, x, z, caix, circ):
        f = self.feet
        for (x0, x1, z0, z1, y0, y1) in caix:
            if f < y1 - 0.25 and f + ALTURA_JOGADOR > y0 and x0 - RAIO < x < x1 + RAIO and z0 - RAIO < z < z1 + RAIO:
                return True
        for (cx, cz, r, h) in circ:
            if h > 0.01 and f < h - 0.25 and (x - cx) ** 2 + (z - cz) ** 2 < (r + RAIO) ** 2:
                return True
        return False

    def chao_em(self, x, z, ref, caix, circ):
        g = 0.0
        for (x0, x1, z0, z1, y0, y1) in caix:
            if y0 <= 0.01 and y1 <= ref + 0.12 and y1 > g and x0 <= x <= x1 and z0 <= z <= z1:
                g = y1
        for (cx, cz, r, h) in circ:
            if 0.01 < h <= 3.0 and h <= ref + 0.12 and h > g and (x - cx) ** 2 + (z - cz) ** 2 <= (r * 0.9) ** 2:
                g = h
        return g

    def atualizar(self, dt):
        self.anim += dt
        if self.corte is not None:
            self._corte_tick(dt)
        if self.intro:
            self.intro_t += dt
            if self.intro_t >= INTRO_DUR:
                self.pular_intro()
        for n in self.nuvens:
            n['az'] += n['v'] * dt
        if self.venceu:
            return
        mp = self.mapa
        self.tempo += dt
        px, pz = self.px, self.pz
        caix = [b for b in mp['caixas'] if b[0] - 3 < px < b[1] + 3 and b[2] - 3 < pz < b[3] + 3]
        circ = [c for c in mp['circ'] if abs(c[0] - px) < c[2] + 3 and abs(c[1] - pz) < c[2] + 3]

        # movimento do joystick (analógico) com suavização
        k = min(1.0, 12.0 * dt)
        self.vel_f += (self.joy_y - self.vel_f) * k
        self.vel_l += (self.joy_x - self.vel_l) * k
        yaw = math.radians(self.yaw)
        fx, fz = math.sin(yaw), math.cos(yaw)
        rx, rz = math.cos(yaw), -math.sin(yaw)
        vel = VEL * (1.6 if self.correr else 1.0)
        dx = (fx * self.vel_f + rx * self.vel_l) * vel * dt
        dz = (fz * self.vel_f + rz * self.vel_l) * vel * dt
        fant = self.cheats.get('fantasma')
        if fant or not self.bloqueado(px + dx, pz, caix, circ):
            px += dx
        if fant or not self.bloqueado(px, pz + dz, caix, circ):
            pz += dz
        # farfalhar dos arbustos (sem colisão)
        self.t_arbusto -= dt
        if self.t_arbusto <= 0.0 and (abs(dx) + abs(dz)) > 1e-4:
            for (cx, cz, r, h) in circ:
                if h < 0.01 and (px - cx) ** 2 + (pz - cz) ** 2 < (r + 0.15) ** 2:
                    self.sfx.tocar('arbusto', 0.8)
                    self.t_arbusto = 0.55
                    break
        x0, x1, z0, z1 = mp['limite']
        self.px = max(x0, min(x1, px))
        self.pz = max(z0, min(z1, pz))

        # gravidade, pulo, chão e teto
        feet_antes = self.feet
        if self.cheats.get('voar'):
            self.feet += (self.alt_alvo - self.feet) * min(1.0, 4.0 * dt)
            self.vy = 0.0
            g = self.chao_em(self.px, self.pz, max(feet_antes, self.feet), caix, circ)
            if self.feet <= g + 0.02:
                self.feet = g
                self.alt_alvo = max(self.alt_alvo, g) if self.alt_alvo > g else g
                self.no_chao = True
            else:
                self.no_chao = False
        else:
            self.vy -= GRAV * dt
            self.feet += self.vy * dt
            g = self.chao_em(self.px, self.pz, feet_antes, caix, circ)
            if self.feet <= g:
                self.feet = g
                self.vy = 0.0
                self.no_chao = True
            else:
                self.no_chao = False
        for (tx0, tx1, tz0, tz1, ty) in mp['tetos']:
            if tx0 <= self.px <= tx1 and tz0 <= self.pz <= tz1 and self.feet + ALTURA_JOGADOR + 0.05 > ty:
                self.feet = ty - ALTURA_JOGADOR - 0.05
                if self.vy > 0:
                    self.vy = 0.0

        # animação de caminhada
        mag = min(1.0, math.hypot(self.vel_f, self.vel_l))
        alvo = mag if self.no_chao else 0.0
        self.bob_amp += (alvo - self.bob_amp) * min(1.0, 8.0 * dt)
        if self.no_chao and mag > 0.05:
            self.fase += dt * (8.0 + 5.0 * mag)

        # gemas
        py = self.feet + 0.9
        for gm in self.gemas:
            if gm[3] and (gm[0] - self.px) ** 2 + (gm[1] - py) ** 2 + (gm[2] - self.pz) ** 2 < 1.4 ** 2:
                gm[3] = False
                if len(gm) > 5:
                    self.inv['cristal'] = self.inv.get('cristal', 0) + 1
                else:
                    self.coletadas += 1
                    self.inv['gema'] += 1
                if self.mundo is not None:
                    salvar_mundos()
        if self.total and self.coletadas >= self.total:
            self.venceu = True
            self.soltar_controles()
            if self.ao_vencer:
                self.ao_vencer(self.tempo)

    # ---------- Projeção 3D -> 2D ----------
    def para_camera(self, p):
        cx, cy, cz = self.cam
        cyaw, syaw, cp, sp = self.trig
        tx, ty, tz = p[0] - cx, p[1] - cy, p[2] - cz
        rx = tx * cyaw - tz * syaw
        rz = tx * syaw + tz * cyaw
        return rx, ty * cp - rz * sp, ty * sp + rz * cp

    def dir_camera(self, d):
        cyaw, syaw, cp, sp = self.trig
        rx = d[0] * cyaw - d[2] * syaw
        rz = d[0] * syaw + d[2] * cyaw
        return rx, d[1] * cp - rz * sp, d[1] * sp + rz * cp

    def projetar_cam(self, cam_pts, uvs):
        """cam_pts no espaço da câmera (x direita, y cima, z frente). Corta no plano próximo e projeta."""
        n = len(cam_pts)
        saida = []
        for i in range(n):
            p1 = cam_pts[i]
            p2 = cam_pts[(i + 1) % n]
            d1 = p1[2] >= Z_NEAR
            d2 = p2[2] >= Z_NEAR
            if d1:
                saida.append((p1, uvs[i] if uvs else None))
            if d1 != d2:
                t = (Z_NEAR - p1[2]) / (p2[2] - p1[2])
                q = (p1[0] + t * (p2[0] - p1[0]), p1[1] + t * (p2[1] - p1[1]), Z_NEAR)
                if uvs:
                    a, b = uvs[i], uvs[(i + 1) % n]
                    saida.append((q, (a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1]))))
                else:
                    saida.append((q, None))
        if len(saida) < 3:
            return None
        w, h, f = self.width, self.height, self.foco
        res = []
        minx = miny = 1e9
        maxx = maxy = -1e9
        for (rx, ry, fz), uv in saida:
            sx = rx * f / fz + w * 0.5
            sy = ry * f / fz + h * 0.5
            res.append((sx, sy, uv))
            minx, maxx = min(minx, sx), max(maxx, sx)
            miny, maxy = min(miny, sy), max(maxy, sy)
        if maxx < 0 or minx > w or maxy < 0 or miny > h:
            return None
        return res

    def projetar(self, verts, uvs=None):
        # caminho rápido: tudo na frente do plano próximo (o caso comum) -> transforma e projeta sem chamadas extras
        cx, cy, cz = self.cam
        cyaw, syaw, cp, sp = self.trig
        f = self.foco
        w, h = self.width, self.height
        hw, hh = w * 0.5, h * 0.5
        res = []
        minx = miny = 1e9
        maxx = maxy = -1e9
        i = 0
        for p in verts:
            tx, ty, tz = p[0] - cx, p[1] - cy, p[2] - cz
            rx = tx * cyaw - tz * syaw
            rz = tx * syaw + tz * cyaw
            fz = ty * sp + rz * cp
            if fz < Z_NEAR:
                return self.projetar_cam([self.para_camera(q) for q in verts], uvs)
            k = f / fz
            sx = rx * k + hw
            sy = (ty * cp - rz * sp) * k + hh
            res.append((sx, sy, uvs[i] if uvs else None))
            i += 1
            if sx < minx:
                minx = sx
            if sx > maxx:
                maxx = sx
            if sy < miny:
                miny = sy
            if sy > maxy:
                maxy = sy
        if maxx < 0 or minx > w or maxy < 0 or miny > h or (maxx - minx < 2.0 and maxy - miny < 2.0):
            return None
        return res

    def tingir(self, cor, d, neblina, emissivo=False):
        mp = self.mapa
        if mp['escuro']:
            if emissivo:
                return cor
            fade = max(0.0, min(1.0, (self.dmax - d) / 8.0))
            k = max(1.0 / (1.0 + (d / 11.0) ** 2), 0.07) * fade
            return (min(1.0, cor[0] * k * 1.06), min(1.0, cor[1] * k), min(1.0, cor[2] * k * 0.88))
        if neblina and mp['neblina']:
            fim = self.dmax * 0.96
            t = (d - fim * 0.30) / (fim * 0.70)
            if t > 0:
                t = min(1.0, t)
                return misturar(cor, CEU_HORIZ, t * t * (3 - 2 * t))
        return cor

    # ---------- Itens de desenho ----------
    def _subdiv(self, verts, teto=8):
        """Quantas divisões uma face texturizada precisa para a textura não entortar de perto."""
        cam = self.cam
        v0, v1, v2, v3 = verts
        pts = list(verts)
        for i in range(4):
            a, bb = verts[i], verts[(i + 1) % 4]
            pts.append(((a[0] + bb[0]) / 2, (a[1] + bb[1]) / 2, (a[2] + bb[2]) / 2))
        pts.append(((v0[0] + v2[0]) / 2, (v0[1] + v2[1]) / 2, (v0[2] + v2[2]) / 2))
        dmin = min(math.sqrt((p[0] - cam[0]) ** 2 + (p[1] - cam[1]) ** 2 + (p[2] - cam[2]) ** 2) for p in pts)
        if dmin > 15.0 or (teto <= 2 and dmin > 8.0):
            return 1
        s1 = math.sqrt((v1[0] - v0[0]) ** 2 + (v1[1] - v0[1]) ** 2 + (v1[2] - v0[2]) ** 2)
        s2 = math.sqrt((v3[0] - v0[0]) ** 2 + (v3[1] - v0[1]) ** 2 + (v3[2] - v0[2]) ** 2)
        k = (0.80, 0.55, 0.40)[self.detalhe]
        n = math.ceil(max(s1, s2) / max(dmin * k, 0.3))
        n = int(n * (0.55 + 0.45 * self.qual) + 0.5)
        return max(1, min(teto, n))

    def _dividir(self, verts, uvs, n):
        def bil(P, u, v):
            return tuple(P[0][k] + (P[1][k] - P[0][k]) * u + (P[3][k] - P[0][k]) * v for k in range(len(P[0])))
        res = []
        for i in range(n):
            for j in range(n):
                u0, u1, v0, v1 = i / float(n), (i + 1) / float(n), j / float(n), (j + 1) / float(n)
                cs = ((u0, v0), (u1, v0), (u1, v1), (u0, v1))
                res.append(([bil(verts, u, v) for u, v in cs], [bil(uvs, u, v) for u, v in cs]))
        return res

    def itens_objeto(self, ob, d):
        cam = self.cam
        faces = ob[4]          # sempre a mesma malha (sem trocar de modelo/textura com a distância)
        neb = ob[6]
        itens = []
        for verts, n, cor, tex, uvs in faces:
            v0 = verts[0]
            if n[0] * (cam[0] - v0[0]) + n[1] * (cam[1] - v0[1]) + n[2] * (cam[2] - v0[2]) <= 0:
                continue
            texobj = None
            c = cor
            if tex:
                texobj, media = self.texs[tex]
                if not self.texturas:
                    texobj = None
                if texobj is None:
                    c = (cor[0] * media[0], cor[1] * media[1], cor[2] * media[2])
            c = self.tingir(c, d, neb)
            if texobj is not None and uvs and len(verts) == 4 and tex not in ('folhas', 'casca', 'rocha'):
                nn = self._subdiv(verts, 2 if tex == 'grama' else 8)
                if nn > 1:
                    for sv, su in self._dividir(verts, uvs, nn):
                        pts = self.projetar(sv, su)
                        if pts:
                            itens.append(('p', pts, c, texobj))
                    continue
            pts = self.projetar(verts, uvs)
            if pts:
                itens.append(('p', pts, c, texobj))
        return itens

    # ---------- Personagem (corpo inteiro) ----------
    def _faces_personagem(self, primeira, e=None, camisa=None, det=True):
        e = e or self
        yb = math.radians(e.corpo_yaw)
        fx, fz = math.sin(yb), math.cos(yb)
        rx, rz = math.cos(yb), -math.sin(yb)
        px, pz, fy = e.px, e.pz, e.feet
        recuo = -0.10 if primeira else 0.0
        amp = 0.06 + 0.94 * e.bob_amp
        no_ar = not e.no_chao
        t = self.anim
        rebote = 0.020 * amp * abs(math.sin(e.fase)) if not no_ar else 0.0
        respira = 0.006 * math.sin(t * 2.0) * (1.0 - amp)
        incl = 0.03 + 0.11 * amp                      # inclina o corpo para a frente ao correr
        giro = math.sin(e.fase) * 0.16 * amp          # ombros giram contra os quadris
        PELE = getattr(e, 'pele', None) or (0.93, 0.74, 0.60)
        CAB = getattr(e, 'cab', None) or (0.20, 0.14, 0.10)
        CAMISA = camisa or getattr(e, 'roupa', None) or (0.80, 0.66, 0.38)
        CALCA = getattr(e, 'calca', None) or (0.25, 0.28, 0.36)
        OLHO = getattr(e, 'olho', None) or (0.22, 0.14, 0.08)
        fem = getattr(e, 'sexo', 'm') == 'f'
        estilo = getattr(e, 'estilo', 0)
        esc = 0.95 if fem else 1.0
        swing = math.sin(e.fase) * 0.05 * amp
        COURO, SOLA = (0.30, 0.20, 0.12), (0.92, 0.90, 0.85)
        faces = []

        def L(a, y, f):                               # quadris / pernas
            a, y, f = a * esc, y * esc, f * esc
            return (px + rx * a + fx * (f + recuo), fy + y + rebote, pz + rz * a + fz * (f + recuo))

        def U(a, y, f):                               # tronco, cabeça e braços (inclina e gira)
            k = max(0.0, y - 0.95)
            th = giro * min(1.25, k / 0.55)
            c, s = math.cos(th), math.sin(th)
            a2, f2 = a * c + f * s, -a * s + f * c
            return L(a2, y + (respira if y > 1.2 else 0.0), f2 + incl * k)

        hy = 0.0
        cam_yaw = getattr(e, 'yaw', None)
        if cam_yaw is not None and not primeira:
            hy = max(-0.8, min(0.8, math.radians((cam_yaw - e.corpo_yaw + 180.0) % 360.0 - 180.0) * 0.55))
        chy, shy = math.cos(hy), math.sin(hy)

        def Hd(a, y, f):                              # cabeça gira para onde a câmera olha
            return U(a * chy + f * shy, y - 0.025, -a * shy + f * chy)

        def poli(q, n, cor, tex=None, uv=None, vies=0.0):
            faces.append((q, n, cor, vies, tex if uv else None, uv))

        def membro(p0, p1, r0, r1, lados, cor, vies=0.0, tex=None):
            for q, n, c, uv in prisma_livre(p0, p1, r0, r1, lados, cor, True):
                faces.append((q, n, c, vies, tex if uv else None, uv))

        def tubo(T, niveis, lados, cor, tex=None, fase0=0.0, topo=False, vies=0.0):
            """Casca elíptica entre níveis (y, rx, rz, fo): torso, mochila..."""
            aneis = []
            for (y, rxx, rzz, fo) in niveis:
                aneis.append([T(rxx * math.cos(fase0 + 2 * math.pi * k / lados), y,
                                fo + rzz * math.sin(fase0 + 2 * math.pi * k / lados)) for k in range(lados)])
            per = 2 * math.pi * (niveis[0][1] + niveis[0][2]) * 0.5
            K = max(1.0, per / 0.30)
            vv = 0.0
            for i in range(len(aneis) - 1):
                A, B = aneis[i], aneis[i + 1]
                dv = abs(niveis[i + 1][0] - niveis[i][0]) / 0.30
                cen = (sum(p[0] for p in A) / lados, sum(p[1] for p in A) / lados, sum(p[2] for p in A) / lados)
                for k in range(lados):
                    j = (k + 1) % lados
                    q = [A[k], A[j], B[j], B[k]]
                    n = normalizar(cross(sub(A[j], A[k]), sub(B[k], A[k])))
                    if n is None:
                        continue
                    mx = sum(p[0] for p in q) / 4.0
                    my = sum(p[1] for p in q) / 4.0
                    mz = sum(p[2] for p in q) / 4.0
                    if dot(n, (mx - cen[0], 0.0, mz - cen[2])) < 0:
                        n = (-n[0], -n[1], -n[2])
                    uv = [(K * k / lados, vv), (K * (k + 1) / lados, vv), (K * (k + 1) / lados, vv + dv), (K * k / lados, vv + dv)]
                    poli(q, n, cor, tex, uv, vies)
                vv += dv
            if topo:
                poli(list(aneis[-1]), (0.0, 1.0, 0.0), cor, None, None, vies)

        def bola(T, c, r, cor, tex=None, lados=6, an=3, sx=1.0, sy=1.0, sz=1.0, filtro=None, vies=0.0):
            lats = [-math.pi / 2 + math.pi * (k + 1) / (an + 1) for k in range(an)]
            lons = [2 * math.pi * i / lados for i in range(lados)]

            def pt(lat, lon):
                a = math.cos(lat) * math.sin(lon)
                f = math.cos(lat) * math.cos(lon)
                y = math.sin(lat)
                return T(c[0] + r * sx * a, c[1] + r * sy * y, c[2] + r * sz * f), (a, y, f)

            g = [[pt(la, lo) for lo in lons] for la in lats]
            base = (T(c[0], c[1] - r * sy, c[2]), (0, -1, 0))
            topo = (T(c[0], c[1] + r * sy, c[2]), (0, 1, 0))
            quads = []
            for i in range(lados):
                j = (i + 1) % lados
                quads.append([base, g[0][j], g[0][i]])
                for k in range(an - 1):
                    quads.append([g[k][i], g[k][j], g[k + 1][j], g[k + 1][i]])
                quads.append([g[-1][i], g[-1][j], topo])
            cw = T(c[0], c[1], c[2])
            for qd in quads:
                la = sum(p[1][0] for p in qd) / len(qd)
                ly = sum(p[1][1] for p in qd) / len(qd)
                lf = sum(p[1][2] for p in qd) / len(qd)
                if filtro is not None and not filtro(la, ly, lf):
                    continue
                wq = [p[0] for p in qd]
                mx = sum(p[0] for p in wq) / len(wq)
                my = sum(p[1] for p in wq) / len(wq)
                mz = sum(p[2] for p in wq) / len(wq)
                n = normalizar((mx - cw[0], (my - cw[1]) / (sy * sy + 1e-6), mz - cw[2]))
                if n:
                    uv = [(0.0, 0.0), (1.0, 0.0), (1.0, 1.0), (0.0, 1.0)] if len(wq) == 4 else None
                    poli(wq, n, cor, tex, uv, vies)

        # ---------- tronco ----------
        sw = 0.88 if fem else 1.0                     # ombros mais estreitos
        qd = 1.08 if fem else 1.0                     # quadris
        cint = 0.92 if fem else 1.0
        if not fem:
            tubo(U, [(0.86, 0.150, 0.100, 0.0), (0.98, 0.162, 0.106, 0.0), (1.08, 0.158, 0.104, 0.0)], 8, CALCA, 'jeans')
            tubo(U, [(1.05, 0.166, 0.110, 0.0), (1.09, 0.166, 0.110, 0.0)], 8, COURO, 'couro')              # cinto
        else:
            tubo(U, [(0.86, 0.150, 0.100, 0.0), (0.98, 0.170, 0.108, 0.0), (1.12, 0.150, 0.100, 0.0)], 8, CALCA, 'tecido')
            tubo(U, [(1.12, 0.150, 0.100, 0.0), (0.96, 0.215, 0.150, 0.0), (0.66, 0.272, 0.200, 0.0)], 10, CALCA, 'tecido')   # saia
        tubo(U, [(1.07 if not fem else 1.10, 0.160 * qd * cint, 0.106, 0.0), (1.22, 0.154 * cint, 0.102, 0.0),
                 (1.35, 0.176 * sw, 0.112, 0.0 if not fem else 0.012), (1.44, 0.198 * sw, 0.106, 0.0),
                 (1.49, 0.118 * sw, 0.080, 0.0)], 8, CAMISA, 'tecido', 0.0, True)
        if not primeira:
            tubo(U, [(1.47, 0.062, 0.060, 0.0), (1.60, 0.050, 0.050, 0.0)], 6, PELE, 'pele')               # pescoço
            tubo(U, [(1.465, 0.088, 0.080, 0.0), (1.505, 0.074, 0.068, 0.0)], 8, (0.93, 0.92, 0.88), 'tecido')   # gola
            if det:                                                                                       # mochila
                MOCH = (0.52, 0.33, 0.20)
                tubo(U, [(0.98, 0.17, 0.085, -0.175), (1.40, 0.17, 0.085, -0.175)], 4, MOCH, 'couro', math.pi / 4, True)
                tubo(U, [(1.06, 0.15, 0.04, -0.235), (1.20, 0.15, 0.04, -0.235)], 4, (0.42, 0.26, 0.15), 'couro', math.pi / 4, True)
                for sd in (-1, 1):
                    membro(U(sd * 0.105, 1.45, -0.10), U(sd * 0.105, 1.45, 0.06), 0.022, 0.022, 4, (0.36, 0.23, 0.14), 0.05)
                    membro(U(sd * 0.105, 1.45, 0.06), U(sd * 0.095, 1.15, 0.10), 0.020, 0.020, 4, (0.36, 0.23, 0.14), 0.05)
        # ---------- pernas ----------
        for lado in (1, -1):
            ph = e.fase + (0.0 if lado == 1 else math.pi)
            if no_ar:
                phi, psi = 0.55 * (1 if lado == 1 else 0.6), -0.25
            else:
                phi = math.sin(ph) * 0.62 * amp
                psi = phi - 1.0 * amp * max(0.0, math.cos(ph))
            hx = lado * 0.088
            quad = L(hx, 0.95, 0)
            jy = 0.95 - 0.44 * math.cos(phi)
            jf = 0.44 * math.sin(phi)
            joe = L(hx, jy, jf)
            ty = jy - 0.43 * math.cos(psi)
            tf = jf + 0.43 * math.sin(psi)
            tor = L(hx, ty, tf)
            if fem:
                membro(quad, joe, 0.078, 0.060, 7, PELE, 0.0, 'pele')
                membro(joe, tor, 0.060, 0.044, 7, PELE, 0.0, 'pele')
                membro(L(hx, ty + 0.085, tf), L(hx, ty + 0.02, tf), 0.047, 0.050, 7, (0.95, 0.94, 0.92), 0.0, 'tecido')   # meia
            else:
                membro(quad, joe, 0.088, 0.068, 7, CALCA, 0.0, 'jeans')
                membro(joe, tor, 0.068, 0.050, 7, CALCA, 0.0, 'jeans')
                membro(L(hx, ty + 0.045, tf), L(hx, ty + 0.0, tf), 0.058, 0.060, 7, (0.20, 0.17, 0.15), 0.0, 'couro')   # cano do sapato
            ponta = L(hx, ty - 0.03, tf + 0.205)
            membro(L(hx, ty + 0.035, tf - 0.045), ponta, 0.062, 0.050, 7, SAPATO_COR(e), 0.0, 'couro')
            membro(L(hx, ty - 0.055, tf - 0.05), L(hx, ty - 0.055, tf + 0.215), 0.066, 0.055, 4, SOLA, 0.0)
        # ---------- braços ----------
        if not primeira:
            for lado in (1, -1):
                ph = e.fase + (0.0 if lado == 1 else math.pi)
                th = 0.9 if no_ar else -math.sin(ph) * 0.62 * amp
                if lado == 1 and getattr(e, 'golpe', None) is not None:
                    th = 0.5 + 1.9 * abs(math.sin(e.golpe * 3.0 * math.pi))
                th2 = th + 0.30 + 0.50 * amp
                sa = lado * (0.200 if fem else 0.220)
                ombro = U(sa, 1.41, 0)
                d1 = normalizar((lado * 0.10, -math.cos(th), math.sin(th)))
                ey, ea, ef = 1.41 + d1[1] * 0.285, sa + d1[0] * 0.285, d1[2] * 0.285
                cot = U(ea, ey, ef)
                d2 = normalizar((lado * 0.04, -math.cos(th2), math.sin(th2)))
                wy, wa, wf = ey + d2[1] * 0.265, ea + d2[0] * 0.265, ef + d2[2] * 0.265
                pul = U(wa, wy, wf)
                mao = U(wa + d2[0] * 0.095, wy + d2[1] * 0.095, wf + d2[2] * 0.095)
                if det:
                    bola(U, (sa * (0.90 if fem else 1.0), 1.41, 0.0), 0.058, CAMISA, 'tecido', 8, 3)
                membro(ombro, cot, 0.056, 0.047, 7, CAMISA, 0.0, 'tecido')
                membro(cot, pul, 0.044, 0.034, 7, PELE, 0.0, 'pele')
                membro(pul, mao, 0.040, 0.036, 6, PELE, 0.0, 'pele')
                if det:
                    cm = U(wa + d2[0] * 0.125, wy + d2[1] * 0.125, wf + d2[2] * 0.125)
                    membro(mao, cm, 0.040, 0.030, 5, PELE, 0.05, 'pele')
                if lado == 1 and getattr(e, 'mao', None) == 'tocha':
                    membro(U(wa - d2[0] * 0.02, wy - d2[1] * 0.02, wf - d2[2] * 0.02), U(wa + d2[0] * 0.40, wy + d2[1] * 0.40, wf + d2[2] * 0.40), 0.026, 0.020, 5, (0.40, 0.26, 0.14))
                    membro(U(wa + d2[0] * 0.38, wy + d2[1] * 0.38, wf + d2[2] * 0.38), U(wa + d2[0] * 0.52, wy + d2[1] * 0.52, wf + d2[2] * 0.52), 0.05, 0.02, 5, (1.0, 0.65, 0.18), 0.1)
                elif lado == 1 and getattr(e, 'mao', None) in ('gema', 'cristal'):
                    membro(U(wa + d2[0] * 0.04, wy + d2[1] * 0.04, wf + d2[2] * 0.04), U(wa + d2[0] * 0.20, wy + d2[1] * 0.20, wf + d2[2] * 0.20), 0.05, 0.005, 5, (1.0, 0.82, 0.22) if e.mao == 'gema' else (0.35, 0.82, 1.0), 0.1)
                elif lado == 1 and getattr(e, 'machado', False):
                    ponta_c = U(wa + d2[0] * 0.55, wy + d2[1] * 0.55, wf + d2[2] * 0.55)
                    membro(U(wa - d2[0] * 0.02, wy - d2[1] * 0.02, wf - d2[2] * 0.02), ponta_c, 0.022, 0.022, 5, (0.45, 0.30, 0.16))
                    membro(U(wa + d2[0] * 0.47, wy + d2[1] * 0.47, wf + d2[2] * 0.47), U(wa + d2[0] * 0.60, wy + d2[1] * 0.60, wf + d2[2] * 0.60), 0.085, 0.085, 4, (0.72, 0.74, 0.78))
            # ---------- cabeça ----------
            cc = (0.0, 1.685, 0.0)
            ra = 0.112

            def cabelo_zona(la, ly, lf):
                return (ly > 0.42) or (lf < -0.02 and ly > -0.42) or (abs(la) > 0.80 and ly > 0.0 and lf < 0.45)

            lados_c, an_c = (10, 4) if det else (8, 3)
            bola(Hd, cc, ra, PELE, 'pele', lados_c, an_c, 1.0, 1.10, 1.0, lambda la, ly, lf: not cabelo_zona(la, ly, lf))
            bola(Hd, (0.0, 1.692, -0.006), ra * 1.13, CAB, 'cabelo', lados_c, an_c, 1.0, 1.10, 1.02,
                 lambda la, ly, lf: cabelo_zona(la, ly, lf) or (lf > 0.2 and ly > 0.30))
            if det:
                for ea in (-1, 1):
                    bola(Hd, (ea * 0.114, 1.675, -0.004), 0.030, PELE, 'pele', 5, 1, 0.55, 1.0, 1.0)
                    membro(Hd(ea * 0.040, 1.690, 0.106), Hd(ea * 0.040, 1.690, 0.116), 0.015, 0.015, 6, (0.96, 0.95, 0.93), 0.09)
                    membro(Hd(ea * 0.040, 1.690, 0.114), Hd(ea * 0.040, 1.690, 0.123), 0.0095, 0.0095, 6, OLHO, 0.12)
                    membro(Hd(ea * 0.040 + 0.006, 1.696, 0.1225), Hd(ea * 0.040 + 0.006, 1.696, 0.1265), 0.0035, 0.0035, 4, (1.0, 1.0, 1.0), 0.2)   # brilho do olho
                    membro(Hd(ea * 0.040 - 0.024, 1.722 + 0.003 * ea, 0.108), Hd(ea * 0.040 + 0.024, 1.722 - 0.003 * ea, 0.108), 0.0085, 0.0085, 4, CAB, 0.08)
                    bola(Hd, (ea * 0.070, 1.636, 0.092), 0.022, tuple(min(1.0, c * 1.04 + (0.06 if k == 0 else 0.0)) for k, c in enumerate(PELE)), 'pele', 5, 1, 1.0, 0.7, 0.35)   # bochecha
                    if fem:                                                                  # cílios
                        membro(Hd(ea * 0.040 - 0.020, 1.708, 0.112), Hd(ea * 0.040 + 0.020, 1.710, 0.112), 0.006, 0.006, 4, (0.08, 0.06, 0.06), 0.13)
                membro(Hd(0, 1.668, 0.108), Hd(0, 1.650, 0.130), 0.015, 0.007, 5, tuple(c * 0.93 for c in PELE), 0.10)
                if fem:
                    membro(Hd(-0.026, 1.614, 0.106), Hd(0.026, 1.614, 0.106), 0.0085, 0.0085, 4, (0.80, 0.36, 0.42), 0.10)
                else:
                    membro(Hd(-0.026, 1.616, 0.105), Hd(0.0, 1.612, 0.108), 0.0065, 0.0065, 4, (0.62, 0.34, 0.32), 0.10)
                    membro(Hd(0.0, 1.612, 0.108), Hd(0.026, 1.616, 0.105), 0.0065, 0.0065, 4, (0.62, 0.34, 0.32), 0.10)
                # penteados
                if fem and estilo == 0:                                                      # solto, longo
                    tubo(Hd, [(1.66, 0.125, 0.075, -0.075), (1.52, 0.130, 0.070, -0.090), (1.40, 0.115, 0.050, -0.100)], 6, CAB, 'cabelo')
                    for sd in (-1, 1):
                        membro(Hd(sd * 0.112, 1.655, 0.015), Hd(sd * 0.112, 1.50, 0.005), 0.032, 0.026, 5, CAB, 0.0, 'cabelo')
                elif fem:                                                                    # rabo de cavalo
                    membro(Hd(0, 1.745, -0.110), Hd(0, 1.64, -0.20), 0.050, 0.040, 6, CAB, 0.0, 'cabelo')
                    membro(Hd(0, 1.64, -0.20), Hd(swing, 1.38, -0.17), 0.040, 0.014, 6, CAB, 0.0, 'cabelo')
                    membro(Hd(0, 1.735, -0.120), Hd(0, 1.715, -0.140), 0.034, 0.034, 6, (0.85, 0.30, 0.45), 0.05)
                elif estilo == 1:                                                            # espetado
                    for (ax, az) in ((0, 0.03), (-0.06, -0.02), (0.06, -0.02), (-0.03, 0.07), (0.03, 0.07), (0, -0.07)):
                        membro(Hd(ax, 1.78, az), Hd(ax * 1.2, 1.90, az * 1.2), 0.045, 0.004, 4, CAB, 0.0, 'cabelo')
            else:
                for ea in (-0.047, 0.047):
                    membro(Hd(ea, 1.69, 0.108), Hd(ea, 1.69, 0.124), 0.016, 0.016, 5, (0.08, 0.07, 0.07), 0.08)
        return faces

    def itens_personagem(self, d, primeira, e=None, camisa=None):
        cam = self.cam
        lista = []
        for q, n, cor, vies, tex, uv in self._faces_personagem(primeira, e, camisa, d < 16.0):
            if n[0] * (cam[0] - q[0][0]) + n[1] * (cam[1] - q[0][1]) + n[2] * (cam[2] - q[0][2]) <= 0:
                continue
            mx = sum(p[0] for p in q) / len(q)
            my = sum(p[1] for p in q) / len(q)
            mz = sum(p[2] for p in q) / len(q)
            dd = math.sqrt((mx - cam[0]) ** 2 + (my - cam[1]) ** 2 + (mz - cam[2]) ** 2) - vies
            lista.append((dd, q, n, cor, tex, uv))
        lista.sort(key=lambda t: -t[0])
        itens = []
        for dd, q, n, cor, tex, uv in lista:
            texobj = None
            c = sombrear(cor, n)
            if tex and self.texturas:
                texobj, media = self.texs[tex]
                if texobj is not None:
                    c = (min(1.0, c[0] / media[0]), min(1.0, c[1] / media[1]), min(1.0, c[2] / media[2]))
            pts = self.projetar(q, uv if texobj is not None else None)
            if pts:
                itens.append(('p', pts, self.tingir(c, d, False), texobj))
        return itens

    CORES_JOGADOR = ((0.36, 0.62, 0.44), (0.62, 0.40, 0.55), (0.62, 0.55, 0.34), (0.45, 0.52, 0.60))
    CABELOS = ((0.20, 0.14, 0.10), (0.78, 0.60, 0.28), (0.08, 0.07, 0.07), (0.55, 0.24, 0.12))
    CALCAS = ((0.25, 0.28, 0.36), (0.16, 0.18, 0.24), (0.32, 0.26, 0.20), (0.22, 0.30, 0.26))
    PELES = ((0.93, 0.74, 0.60), (0.80, 0.58, 0.42), (0.62, 0.43, 0.30), (0.96, 0.80, 0.68))
    OLHOS = ((0.22, 0.14, 0.08), (0.18, 0.36, 0.55), (0.20, 0.42, 0.26), (0.10, 0.08, 0.07))
    TENIS = ((0.22, 0.20, 0.22), (0.70, 0.22, 0.20), (0.22, 0.40, 0.70), (0.85, 0.82, 0.78))

    def _remotos_suaves(self):
        res = []
        if not self.rede.rodando:
            self.suaves = {}
            return res
        jog = self.rede.jogadores()
        for rid in list(self.suaves):
            if rid not in jog:
                del self.suaves[rid]
        for rid, r in jog.items():
            if r.get('m') != self.chave:
                continue
            e = self.suaves.get(rid)
            if e is None:
                e = SimpleNamespace(px=r['x'], pz=r['z'], feet=r['y'], corpo_yaw=r['yaw'], fase=r['f'],
                                    bob_amp=r['a'], no_chao=not r['ar'],
                                    cab=self.CABELOS[int(rid) % 4], calca=self.CALCAS[int(rid) % 4],
                                    pele=self.PELES[int(rid) % 4], olho=self.OLHOS[int(rid) % 4], tenis=self.TENIS[int(rid) % 4], yaw=r['yaw'],
                                    sexo='m', estilo=0, roupa=None, pf=None)
                self.suaves[rid] = e
            pf = r.get('pf')
            if pf is not None and pf != e.pf:
                e.pf = list(pf)
                p = perfil_de_rede(pf)
                if p:
                    for k, v in atributos_perfil(p).items():
                        setattr(e, k, v)
            e.px += (r['x'] - e.px) * 0.35
            e.pz += (r['z'] - e.pz) * 0.35
            e.feet += (r['y'] - e.feet) * 0.35
            dif = (r['yaw'] - e.corpo_yaw + 180.0) % 360.0 - 180.0
            e.corpo_yaw += dif * 0.35
            e.fase = r['f']
            e.bob_amp += (r['a'] - e.bob_amp) * 0.35
            e.no_chao = not r['ar']
            res.append((rid, e, e.roupa or self.CORES_JOGADOR[int(rid) % 4]))
        return res

    def _rede_tick(self, dt):
        if not self.rede.rodando:
            return
        self.t_rede += dt
        if self.t_rede >= 0.066:
            self.t_rede = 0.0
            self.rede.enviar({'m': self.chave, 'x': round(self.px, 2), 'y': round(self.feet, 2), 'z': round(self.pz, 2),
                              'yaw': round(self.corpo_yaw, 1), 'f': round(self.fase, 2), 'a': round(self.bob_amp, 2),
                              'ar': 0 if self.no_chao else 1, 'pf': perfil_para_rede(PERFIL or perfil_padrao())})

    def _camera_livre(self, x, y, z, piv_y):
        if y < 0.12:
            return False
        mp = self.mapa
        for (x0, x1, z0, z1, y0, y1) in mp['caixas']:
            if x0 - 0.1 < x < x1 + 0.1 and z0 - 0.1 < z < z1 + 0.1 and y0 - 0.1 < y < y1 + 0.1:
                return False
        for (cx, cz, r, h) in mp['circ']:
            if (x - cx) ** 2 + (z - cz) ** 2 < r * r and y < h:
                return False
        for (tx0, tx1, tz0, tz1, ty) in mp['tetos']:
            if tx0 <= x <= tx1 and tz0 <= z <= tz1 and piv_y < ty < y + 0.15:
                return False
        return True

    def _configurar_camera(self):
        """Define self.cam e os ângulos de visão conforme 1ª, 3ª ou 2ª pessoa."""
        bob = 0.04 * math.sin(self.fase * 2.0) * self.bob_amp
        modo = self.camera
        yr, pr = math.radians(self.yaw), math.radians(self.pitch)
        if self.vitrine:
            th = self.anim * 0.55 + math.radians(self.corpo_yaw) + math.pi + 0.5
            piv = (self.px, self.feet + 1.0, self.pz)
            self.pivo = piv
            R = 3.3
            while R > 1.2 and not self._camera_livre(piv[0] + math.sin(th) * R, piv[1] + 0.35, piv[2] + math.cos(th) * R, piv[1]):
                R -= 0.3
            cam = (piv[0] + math.sin(th) * R, piv[1] + 0.35, piv[2] + math.cos(th) * R)
            # mira um pouco à esquerda do personagem para ele aparecer no lado direito da tela
            rxv, rzv = math.cos(th), -math.sin(th)
            alvo = (piv[0] - rxv * 0.0, piv[1] - 0.05, piv[2] - rzv * 0.0)
            vx, vy, vz = alvo[0] - cam[0], alvo[1] - cam[1], alvo[2] - cam[2]
            yaw = math.atan2(vx, vz)
            yaw -= 0.34                                 # gira a visão -> personagem vai para a direita
            vl = math.sqrt(vx * vx + vy * vy + vz * vz) or 1.0
            return cam, math.degrees(yaw), math.degrees(math.asin(max(-1.0, min(1.0, vy / vl))))
        if self.intro:
            k = min(1.0, self.intro_t / INTRO_DUR)
            e = k * k * (3.0 - 2.0 * k)
            piv = (self.px, self.feet + 1.55, self.pz)
            self.pivo = piv
            aberto = self.chave in ('aberto', 'mundo')
            R = (3.3 + (14.0 if aberto else 3.0) * (1.0 - e))
            H = (-math.sin(pr) * 3.3) * e + (6.5 if aberto else 1.6) * (1.0 - e)
            th = yr + math.pi + 2.2 * (1.0 - e)
            dxh, dzh = math.sin(th), math.cos(th)
            fx, fy, fz = dxh * R, H, dzh * R
            ln = math.sqrt(fx * fx + fy * fy + fz * fz)
            t = 0.35
            livre = 0.35
            while t <= ln:
                if not self._camera_livre(piv[0] + fx / ln * t, piv[1] + fy / ln * t, piv[2] + fz / ln * t, piv[1]):
                    break
                livre = t
                t += 0.25
            f = min(ln, livre) / ln
            cam = (piv[0] + fx * f, piv[1] + fy * f, piv[2] + fz * f)
            vx, vy, vz = piv[0] - cam[0], piv[1] - cam[1], piv[2] - cam[2]
            vl = math.sqrt(vx * vx + vy * vy + vz * vz) or 1.0
            return cam, math.degrees(math.atan2(vx, vz)), math.degrees(math.asin(max(-1.0, min(1.0, vy / vl))))
        if modo == 'primeira':
            self.pivo = None
            self.corpo_yaw = self.yaw
            return (self.px, self.feet + ALTURA_OLHO + bob, self.pz), self.yaw, self.pitch
        piv = (self.px, self.feet + 1.55, self.pz)
        self.pivo = piv
        dv = (math.sin(yr) * math.cos(pr), math.sin(pr), math.cos(yr) * math.cos(pr))
        sinal = -1.0 if modo == 'terceira' else 1.0
        dist = 3.3 if modo == 'terceira' else 2.8
        t = 0.35
        livre = 0.35
        while t <= dist:
            x, y, z = piv[0] + sinal * dv[0] * t, piv[1] + sinal * dv[1] * t, piv[2] + sinal * dv[2] * t
            if not self._camera_livre(x, y, z, piv[1]):
                break
            livre = t
            t += 0.2
        dist = max(0.5, min(dist, livre))
        cam = (piv[0] + sinal * dv[0] * dist, piv[1] + sinal * dv[1] * dist, piv[2] + sinal * dv[2] * dist)
        # corpo vira para onde anda
        ddx, ddz = self.px - self.ult_pos[0], self.pz - self.ult_pos[1]
        self.ult_pos = (self.px, self.pz)
        if ddx * ddx + ddz * ddz > 1e-6:
            alvo = math.degrees(math.atan2(ddx, ddz))
            dif = (alvo - self.corpo_yaw + 180.0) % 360.0 - 180.0
            self.corpo_yaw += dif * 0.28
        if modo == 'terceira':
            return cam, self.yaw, self.pitch
        return cam, self.yaw + 180.0, -self.pitch

    def itens_gema(self, idx, g, d):
        gx, gy, gz = g[0], g[1] + math.sin(self.anim * 2.0 + idx) * 0.15, g[2]
        centro = (gx, gy, gz)
        cam = self.cam
        itens = []
        rx, ry, fz = self.para_camera(centro)
        if fz > 0.3:
            sx = rx * self.foco / fz + self.width * 0.5
            sy = ry * self.foco / fz + self.height * 0.5
            for raio, alfa in ((1.30, 0.05), (0.95, 0.07), (0.68, 0.10), (0.46, 0.14)):
                itens.append(('e', sx, sy, min(raio * self.foco / fz, self.height * 0.3), (0.45, 0.85, 1.0) if len(g) > 5 else (1.0, 0.86, 0.35), alfa))
        ang = self.anim * 1.5
        r = 0.40
        anel = [(gx + r * math.cos(ang + k * math.pi / 3), gy, gz + r * math.sin(ang + k * math.pi / 3))
                for k in range(6)]
        topo = (gx, gy + 0.62, gz)
        base = (gx, gy - 0.62, gz)
        for k in range(6):
            a, b = anel[k], anel[(k + 1) % 6]
            for tri in ([topo, a, b], [base, b, a]):
                n = normalizar(cross(sub(tri[1], tri[0]), sub(tri[2], tri[0])))
                if n is None:
                    continue
                cf = ((tri[0][0] + tri[1][0] + tri[2][0]) / 3.0, (tri[0][1] + tri[1][1] + tri[2][1]) / 3.0,
                      (tri[0][2] + tri[1][2] + tri[2][2]) / 3.0)
                if dot(n, sub(cf, centro)) < 0:
                    n = (-n[0], -n[1], -n[2])
                if dot(n, sub(cam, tri[0])) <= 0:
                    continue
                pts = self.projetar(tri)
                if pts:
                    br = 0.78 + 0.30 * max(0.0, dot(n, LUZ))
                    if len(g) > 5:
                        itens.append(('p', pts, (min(1.0, 0.35 * br), min(1.0, 0.82 * br), min(1.0, 1.0 * br)), None))
                    else:
                        itens.append(('p', pts, (min(1.0, 1.0 * br), min(1.0, 0.82 * br), min(1.0, 0.22 * br)), None))
        return itens

    def itens_bracos(self):
        amp = 0.06 + 0.94 * self.bob_amp
        no_ar = 0.0 if self.no_chao else 0.35
        resp = math.sin(self.anim * 1.7) * 0.025
        L = self.dir_camera(LUZ)
        escuro = 0.85 if self.mapa['escuro'] else 1.0
        faces = []
        for lado in (1, -1):
            swing = math.sin(self.fase + (0.0 if lado == 1 else math.pi)) * 0.28 * amp
            a1 = 0.75 + swing + resp * 0.5 - no_ar * 0.5
            a2 = 2.0 + swing * 0.6 - no_ar * 0.4
            a3 = a2 + 0.25

            def dv(a, inv):
                return normalizar((-lado * inv, -math.cos(a), math.sin(a)))

            S = (0.34 * lado, -0.40 + resp * 0.4, -0.10)
            d1, d2, d3 = dv(a1, 0.12), dv(a2, 0.18), dv(a3, 0.20)
            E = (S[0] + d1[0] * 0.38, S[1] + d1[1] * 0.38, S[2] + d1[2] * 0.38)
            M = (E[0] + d2[0] * 0.16, E[1] + d2[1] * 0.16, E[2] + d2[2] * 0.16)
            W = (E[0] + d2[0] * 0.46, E[1] + d2[1] * 0.46, E[2] + d2[2] * 0.46)
            Hd = (W[0] + d3[0] * 0.13, W[1] + d3[1] * 0.13, W[2] + d3[2] * 0.13)
            Tb = normalizar((-lado * 0.6, 0.35, 0.7))
            T0 = (W[0] - lado * 0.025, W[1] + 0.03, W[2] + 0.02)
            T1 = (T0[0] + Tb[0] * 0.075, T0[1] + Tb[1] * 0.075, T0[2] + Tb[2] * 0.075)
            for (p0, p1, r0, r1, lados, cor) in ((S, E, 0.064, 0.056, 8, MANGA), (E, M, 0.058, 0.054, 8, MANGA),
                                                 (M, W, 0.047, 0.038, 8, PELE), (W, Hd, 0.050, 0.047, 8, PELE),
                                                 (T0, T1, 0.019, 0.015, 5, PELE)):
                faces += prisma_livre(p0, p1, r0, r1, lados, cor)
        itens = []
        orden = []
        for q, n, cor in faces:
            if dot(n, (-q[0][0], -q[0][1], -q[0][2])) <= 0:
                continue
            prof = sum(p[2] for p in q) / len(q)
            br = (0.50 + 0.50 * max(0.0, dot(n, L))) * escuro
            orden.append((prof, q, (cor[0] * br, cor[1] * br, cor[2] * br)))
        orden.sort(key=lambda t: -t[0])
        for prof, q, cor in orden:
            pts = self.projetar_cam(q, None)
            if pts:
                itens.append(('p', pts, cor, None))
        return itens

    def coletar(self, lista, cam, fwd, rgt, K, ordenar):
        saida = []
        cx, cy, cz = cam
        for ob in lista:
            dx, dy, dz = ob[0] - cx, ob[1] - cy, ob[2] - cz
            r = ob[3]
            d2 = dx * dx + dy * dy + dz * dz
            lim = self.dmax + r
            if d2 > lim * lim or (r < 0.45 and d2 > self.lim_peq):   # coisas bem pequenas só aparecem de perto
                continue
            fz = dx * fwd[0] + dy * fwd[1] + dz * fwd[2]
            if fz < -r:
                continue
            if abs(dx * rgt[0] + dz * rgt[2]) > (fz + r) * K + r:
                continue
            saida.append((math.sqrt(d2), ob))
        return saida

    # ---------- Céu: degradê, sol e nuvens suaves ----------
    def pintar_ceu(self, w, h, hy):
        mp = self.mapa
        if not mp['ceu']:
            Color(0.03, 0.03, 0.04, 1)
            Rectangle(pos=(0, 0), size=(w, h))
            return
        Color(*CEU_HORIZ)
        Rectangle(pos=(0, 0), size=(w, h))
        bh = max(6.0, h * 0.025)
        i0 = max(0, int(-hy / bh))
        i1 = int((h - hy) / bh) + 1
        for i in range(i0, i1 + 1):
            y0 = hy + i * bh
            if y0 > h:
                break
            t = min(1.0, (i * bh) / (self.foco * 1.7))
            t = t ** 0.8
            cor = misturar(CEU_HORIZ, CEU_MEIO, t * 2) if t < 0.5 else misturar(CEU_MEIO, CEU_TOPO, (t - 0.5) * 2)
            Color(*cor)
            Rectangle(pos=(0, y0), size=(w, bh + 1))
        # sol: brilho em camadas, bem suave
        rx, ry, fz = self.dir_camera(LUZ)
        if fz > 0.05:
            sx = rx / fz * self.foco + w * 0.5
            sy = ry / fz * self.foco + h * 0.5
            rr = h * 0.036
            for mult, alfa in ((9.0, 0.025), (6.5, 0.035), (4.6, 0.05), (3.3, 0.07), (2.4, 0.09), (1.7, 0.12), (1.25, 0.18)):
                Color(1.0, 0.96, 0.82, alfa)
                Ellipse(pos=(sx - rr * mult, sy - rr * mult), size=(rr * mult * 2, rr * mult * 2))
            Color(1.0, 0.99, 0.93, 1.0)
            Ellipse(pos=(sx - rr, sy - rr), size=(rr * 2, rr * 2))
        # nuvens: bolinhas macias sobrepostas (base cinza-azulada, topo branco)
        for n in (self.nuvens if self.nuvens_on else ()):
            az, el, s = n['az'], n['el'], n['s']
            d = (math.sin(az) * math.cos(el), math.sin(el), math.cos(az) * math.cos(el))
            rx, ry, fz = self.dir_camera(d)
            if fz < 0.2:
                continue
            esc = self.foco / fz
            cx = rx * esc + w * 0.5
            cy = ry * esc + h * 0.5
            if cx < -s * esc * 3 or cx > w + s * esc * 3 or cy < -s * esc * 2 or cy > h + s * esc * 2:
                continue
            for dx, dy, pr in PUFFS:
                px, py, rad = cx + dx * s * esc, cy + dy * s * esc * 0.7, pr * s * esc
                Color(0.80, 0.86, 0.94, 0.55)
                Ellipse(pos=(px - rad, py - rad * 1.05), size=(rad * 2, rad * 2))
            for dx, dy, pr in PUFFS:
                px, py, rad = cx + dx * s * esc, cy + dy * s * esc * 0.7, pr * s * esc
                Color(1.0, 1.0, 1.0, 0.62)
                Ellipse(pos=(px - rad * 0.93, py - rad * 0.80), size=(rad * 1.86, rad * 1.86))
                Color(1.0, 1.0, 1.0, 0.30)
                Ellipse(pos=(px - rad * 0.55 + rad * 0.12, py - rad * 0.20), size=(rad * 1.1, rad * 1.1))
        self.pintar_colinas(w, h, hy)

    def pintar_colinas(self, w, h, hy):
        """Duas cordilheiras distantes (sem paralaxe) para o horizonte não ficar reto e vazio."""
        if hy < -h * 0.3 or hy > h * 1.2:
            return
        camadas = ((0.022, 0.050, 0.45, 1.0, (0.62, 0.74, 0.84)), (0.010, 0.032, 0.62, 2.3, (0.46, 0.64, 0.62)))
        passo = max(10, int(w / 70))
        for base, amp, mist, fase, cor in camadas:
            col = misturar(cor, CEU_HORIZ, 0.0 if mist > 0.5 else 0.35)
            Color(col[0], col[1], col[2], 1)
            v = []
            idx = 0
            for sx in range(-passo, int(w) + 2 * passo, passo):
                ang = math.atan((sx - w * 0.5) / self.foco)
                az = self.yaw_r + ang
                f = (0.5 + 0.5 * math.sin(az * 2.6 + fase) * 0.55 + 0.5 * math.sin(az * 6.1 + fase * 2) * 0.30
                     + 0.5 * math.sin(az * 13.0 + fase * 3) * 0.15)
                elev = base + amp * f
                sy = hy + math.tan(elev) * self.foco
                v.extend((sx, sy, 0, 0, sx, hy - 4, 0, 0))
            n = len(v) // 4
            Mesh(vertices=v, indices=list(range(n)), mode='triangle_strip')

    def pintar_vinheta(self, w, h):
        if self.vig is None and not self.vig_falhou:
            try:
                N = 64
                buf = bytearray(N * N * 4)
                for y in range(N):
                    for x in range(N):
                        dx, dy = (x - 31.5) / 31.5, (y - 31.5) / 31.5
                        r = min(1.0, math.sqrt(dx * dx + dy * dy) / 1.35)
                        a = int(255 * 0.42 * max(0.0, (r - 0.45) / 0.55) ** 1.8)
                        i = (y * N + x) * 4
                        buf[i + 3] = a
                t = Texture.create(size=(N, N), colorfmt='rgba')
                t.blit_buffer(bytes(buf), colorfmt='rgba', bufferfmt='ubyte')
                self.vig = t
            except Exception:
                self.vig_falhou = True
        if self.vig is not None:
            Color(1, 1, 1, 1)
            Rectangle(texture=self.vig, pos=(0, 0), size=(w, h))

    def pintar_item(self, it):
        if it[0] == 'p':
            pts, cor, tex = it[1], it[2], it[3]
            Color(cor[0], cor[1], cor[2], 1)
            v = []
            if tex is not None:
                for sx, sy, uv in pts:
                    v.extend((sx, sy, uv[0], uv[1]))
                Mesh(vertices=v, indices=list(range(len(pts))), mode='triangle_fan', texture=tex)
            else:
                for sx, sy, uv in pts:
                    v.extend((sx, sy, 0, 0))
                Mesh(vertices=v, indices=list(range(len(pts))), mode='triangle_fan')
        else:
            _, sx, sy, r, cor, alfa = it
            Color(cor[0], cor[1], cor[2], alfa)
            Ellipse(pos=(sx - r, sy - r), size=(2 * r, 2 * r))

    def pintar_lote(self, itens):
        """Pinta os itens na ordem; polígonos seguidos com a mesma textura e cor (quase iguais) viram UMA malha só."""
        run = None
        chave = None
        for it in itens:
            if it[0] != 'p':
                if run:
                    self._flush(run)
                    run = None
                    chave = None
                self.pintar_item(it)
                continue
            pts, cor, tex = it[1], it[2], it[3]
            k = (id(tex), int(cor[0] * 40), int(cor[1] * 40), int(cor[2] * 40))
            if k != chave or (run and len(run[3]) > 12000):
                if run:
                    self._flush(run)
                run = (cor, tex, [], [])
                chave = k
            vs, idx = run[2], run[3]
            b = len(vs) // 4
            if tex is not None:
                for sx, sy, uv in pts:
                    vs.extend((sx, sy, uv[0], uv[1]))
            else:
                for sx, sy, uv in pts:
                    vs.extend((sx, sy, 0, 0))
            for j in range(1, len(pts) - 1):
                idx.extend((b, b + j, b + j + 1))
        if run:
            self._flush(run)

    def _flush(self, run):
        cor, tex, vs, idx = run
        Color(cor[0], cor[1], cor[2], 1)
        if tex is not None:
            Mesh(vertices=vs, indices=idx, mode='triangles', texture=tex)
        else:
            Mesh(vertices=vs, indices=idx, mode='triangles')

    def _agrupar_fundo(self, itens):
        """O chão não se sobrepõe: dentro de cada trecho de mesma textura, junta as cores parecidas."""
        saida = []
        i, n = 0, len(itens)
        while i < n:
            j = i
            t = itens[i][3]
            while j < n and itens[j][3] is t:
                j += 1
            trecho = itens[i:j]
            if len(trecho) > 2:
                trecho.sort(key=lambda it: (int(it[2][0] * 40), int(it[2][1] * 40), int(it[2][2] * 40)))
            saida.extend(trecho)
            i = j
        return saida

    # ---------- Quadro completo ----------
    def desenhar(self):
        w, h = self.width, self.height
        if w < 10 or h < 10 or self.mapa is None:
            return
        mp = self.mapa
        self.cam, yaw_g, pit_g = self._configurar_camera()
        primeira = (self.camera == 'primeira') and not self.intro and not self.vitrine
        yaw, pit = math.radians(yaw_g), math.radians(pit_g)
        self.yaw_r = yaw
        cyaw, syaw, cp, sp = math.cos(yaw), math.sin(yaw), math.cos(pit), math.sin(pit)
        self.trig = (cyaw, syaw, cp, sp)
        self.foco = h * 1.0
        fwd = (syaw * cp, sp, cyaw * cp)
        rgt = (cyaw, 0.0, -syaw)
        K = (w * 0.5 / self.foco) * 1.25
        self.dmax = mp['dist'] * self.qual * self.dist_mult
        self.lod_dist = 22.0 * self.qual
        self.lim_peq = (14.0 + 12.0 * self.qual) ** 2
        orcamento = int(ORCAMENTO_BASE * self.qual)
        cam = self.cam

        fundo = []
        for d, ob in self.coletar(mp['fundo'], cam, fwd, rgt, K, False):
            fundo.extend(self.itens_objeto(ob, d))

        cand = [(d, d, ob) for d, ob in self.coletar(mp['objs'], cam, fwd, rgt, K, True)]
        for idx, g in enumerate(self.gemas):
            if g[3]:
                dx, dy, dz = g[0] - cam[0], g[1] - cam[1], g[2] - cam[2]
                if dx * fwd[0] + dy * fwd[1] + dz * fwd[2] > -1.5:
                    d = math.sqrt(dx * dx + dy * dy + dz * dz)
                    if d < self.dmax:
                        cand.append((d - 1.2, d, (idx, g)))
        for rid, est, cam_cor in self._remotos_suaves():
            dr = math.sqrt((est.px - cam[0]) ** 2 + (est.feet + 1.0 - cam[1]) ** 2 + (est.pz - cam[2]) ** 2)
            if dr < self.dmax:
                cand.append((dr - 0.9, dr, ('R', est, cam_cor)))
        if not primeira:
            dp = math.sqrt((self.pivo[0] - cam[0]) ** 2 + (self.pivo[1] - cam[1]) ** 2 + (self.pivo[2] - cam[2]) ** 2)
            cand.append((dp - 0.9, dp, 'P'))
        queda = self.arvore_caindo()
        if queda is not None:
            dq = math.sqrt((queda[0] - cam[0]) ** 2 + (queda[1] - cam[1]) ** 2 + (queda[2] - cam[2]) ** 2)
            cand.append((dq, dq, queda))
        cand.sort(key=lambda t: t[0])
        usados = []
        total = 0
        for _, d, ob in cand:
            if isinstance(ob, tuple) and ob[0] == 'R':
                usados.append(self.itens_personagem(d, False, ob[1], ob[2]))
                continue
            if ob == 'P':
                usados.append(self.itens_personagem(d, False))
                continue
            if total >= orcamento and (len(ob) == 2 or not (ob[4] and ob[4][0][3])):
                continue   # estouro do orçamento: só deixa de fora o que é pequeno/sem textura; paredes sempre ficam
            if len(ob) == 2 and self.vitrine:
                continue
            itens = self.itens_gema(ob[0], ob[1], d) if len(ob) == 2 else self.itens_objeto(ob, d)
            if itens:
                usados.append(itens)
                total += len(itens)

        corpo = self.itens_personagem(0.5, True) if primeira else []
        bracos = self.itens_bracos() if primeira else []
        hy = h * 0.5 - self.foco * math.tan(pit)

        self.canvas.clear()
        with self.canvas:
            self.pintar_ceu(w, h, hy)
            if mp['neblina']:
                base = self.projetar([(cam[0] - 600, 0, cam[2] - 600), (cam[0] + 600, 0, cam[2] - 600),
                                      (cam[0] + 600, 0, cam[2] + 600), (cam[0] - 600, 0, cam[2] + 600)])
                if base:
                    self.pintar_item(('p', base, CEU_HORIZ, None))
            self.pintar_lote(self._agrupar_fundo(fundo))
            geral = []
            for itens in reversed(usados):
                geral.extend(itens)
            self.pintar_lote(geral)
            self.pintar_lote(corpo)
            self.pintar_lote(bracos)
            self.pintar_vinheta(w, h)
            self.pintar_joystick(w, h)
            if self.intro:
                k = self.intro_t / INTRO_DUR
                barra = h * 0.11 * min(1.0, k * 6.0, (1.0 - k) * 6.0 + 0.2)
                Color(0, 0, 0, 1)
                Rectangle(pos=(0, 0), size=(w, barra))
                Rectangle(pos=(0, h - barra), size=(w, barra))
                if self.intro_t < 0.7:
                    Color(0, 0, 0, 1.0 - self.intro_t / 0.7)
                    Rectangle(pos=(0, 0), size=(w, h))

    def pintar_joystick(self, w, h):
        if self.pausado or self.venceu:
            return
        r = self.joy_raio()
        if self.joy_uid is None:
            ox, oy = max(r * 1.1, w * 0.13), h * 0.30
            kx, ky, forca = ox, oy, 0.5
        else:
            ox, oy = self.joy_o
            kx, ky = self.joy_k
            forca = 1.0
        Color(1, 1, 1, 0.10 * forca)
        Ellipse(pos=(ox - r, oy - r), size=(2 * r, 2 * r))
        Color(1, 1, 1, 0.38 * forca)
        Line(circle=(ox, oy, r), width=1.6)
        Color(1, 1, 1, 0.50 * forca)
        Ellipse(pos=(kx - r * 0.40, ky - r * 0.40), size=(r * 0.80, r * 0.80))

    def loop(self, dt):
        try:
            self.dt_med = self.dt_med * 0.9 + dt * 0.1
            self.n_quadros += 1
            if self.q_modo != 'auto':
                self.qual = {'baixa': 0.5, 'media': 0.75, 'alta': 1.0}[self.q_modo]
            elif self.n_quadros % 15 == 0:   # ajusta a qualidade sozinho conforme o celular aguenta
                if self.dt_med > 0.045:
                    self.qual = max(0.32, self.qual - 0.08)
                elif self.dt_med < 0.029:
                    self.qual = min(1.0, self.qual + 0.03)
            dt = min(dt, 0.05)
            if not self.pausado:
                self.atualizar(dt)
            else:
                self.anim += dt
                for n in self.nuvens:
                    n['az'] += n['v'] * dt
            self._tex_finalizar()
            self._rede_tick(dt)
            self.desenhar()
            if self.hud is not None and self.intro:
                self.hud.text = 'Jogo de Samuel  -  ' + str(self.mapa['nome'])
            elif self.hud is not None:
                self.hud.text = ((f"{1.0 / max(self.dt_med, 0.001):.0f} fps   " if self.fps_on else "") +
                                 (f"Online: {1 + len(self.rede.jogadores())}" if self.rede.rodando else "")).strip()
        except Exception:
            self.erro = traceback.format_exc()
            print(self.erro)
            self.evento.cancel()
            if self.ao_erro:
                self.ao_erro(self.erro)


# ======================= INTERFACE =======================

def _poli(pts):
    v = []
    for px_, py_ in pts:
        v += [px_, py_, 0, 0]
    Mesh(vertices=v, indices=list(range(len(pts))), mode='triangle_fan')


def _arte(nome, cx, cy, u):
    """Mini ilustração de cada mapa (só formas simples, sem azul nem vermelho)."""
    if nome == 'casa':
        Color(0.80, 0.62, 0.40, 1)
        Rectangle(pos=(cx - u * 1.1, cy - u * 1.0), size=(u * 2.2, u * 1.3))
        Color(0.45, 0.30, 0.22, 1)
        _poli([(cx - u * 1.5, cy + u * 0.3), (cx + u * 1.5, cy + u * 0.3), (cx, cy + u * 1.5)])
        Color(0.35, 0.24, 0.16, 1)
        Rectangle(pos=(cx - u * 0.25, cy - u * 1.0), size=(u * 0.5, u * 0.8))
        Color(1, 0.88, 0.5, 1)
        Rectangle(pos=(cx + u * 0.5, cy - u * 0.4), size=(u * 0.4, u * 0.4))
    elif nome == 'arvore':
        Color(0.45, 0.32, 0.22, 1)
        Rectangle(pos=(cx - u * 0.18, cy - u * 1.2), size=(u * 0.36, u * 1.0))
        Color(0.30, 0.62, 0.35, 1)
        Ellipse(pos=(cx - u * 0.9, cy - u * 0.4), size=(u * 1.8, u * 1.5))
        Color(0.42, 0.75, 0.42, 1)
        Ellipse(pos=(cx - u * 0.5, cy + u * 0.1), size=(u * 1.0, u * 0.9))
    elif nome == 'janela':
        Color(0.62, 0.50, 0.40, 1)
        Rectangle(pos=(cx - u * 1.2, cy - u * 1.2), size=(u * 2.4, u * 2.4))
        Color(0.62, 0.80, 0.92, 1)
        Rectangle(pos=(cx - u * 0.9, cy - u * 0.9), size=(u * 1.8, u * 1.8))
        Color(0.30, 0.62, 0.35, 1)
        Rectangle(pos=(cx - u * 0.9, cy - u * 0.9), size=(u * 1.8, u * 0.5))
        Color(0.62, 0.50, 0.40, 1)
        Rectangle(pos=(cx - u * 0.06, cy - u * 0.9), size=(u * 0.12, u * 1.8))
        Rectangle(pos=(cx - u * 0.9, cy - u * 0.06), size=(u * 1.8, u * 0.12))
    elif nome == 'caverna':
        Color(0.40, 0.42, 0.44, 1)
        Ellipse(pos=(cx - u * 1.5, cy - u * 1.2), size=(u * 3.0, u * 2.8))
        Color(0.06, 0.07, 0.08, 1)
        Ellipse(pos=(cx - u * 0.6, cy - u * 1.0), size=(u * 1.2, u * 1.7))
        Rectangle(pos=(cx - u * 0.6, cy - u * 1.2), size=(u * 1.2, u * 1.0))
    # brilho dourado de gema ao lado
    Color(1, 0.84, 0.30, 1)
    _poli([(cx + u * 1.7, cy + u * 0.2), (cx + u * 2.0, cy + u * 0.7), (cx + u * 1.7, cy + u * 1.2),
           (cx + u * 1.4, cy + u * 0.7)])


class Botao(Widget):
    """Botão de vidro escuro (redondo ou em pílula), sem cores berrantes."""

    def __init__(self, texto='', icone=None, forma='pilula', ao_tocar=None, imediato=False, fonte='16sp', repetir=0.0, **kw):
        kw.setdefault('size_hint', (None, None))
        super().__init__(**kw)
        self.icone = icone
        self.forma = forma
        self.ao_tocar = ao_tocar
        self.imediato = imediato
        self.repetir = repetir
        self._rep = None
        self.ativo = False
        self.apertado = False
        self._uid = None
        self.rotulo = Label(text=texto, font_size=fonte, color=(1, 1, 1, 0.95), halign='center', valign='middle')
        self.add_widget(self.rotulo)
        self.bind(pos=self.redesenhar, size=self.redesenhar)
        self.redesenhar()

    def redesenhar(self, *args):
        x, y = self.pos
        w, h = self.size
        r = min(w, h) / 2.0
        cx, cy = x + w / 2.0, y + h / 2.0
        self.canvas.before.clear()
        self.canvas.after.clear()
        brilho = 0.34 if self.apertado else (0.24 if self.ativo else 0.12)
        with self.canvas.before:
            Color(0.05, 0.06, 0.08, 0.55)
            self._forma(x, y, w, h, r)
            Color(1, 1, 1, brilho)
            self._forma(x, y, w, h, r)
            Color(1, 1, 1, 0.60 if self.ativo else 0.30)
            if self.forma == 'circulo':
                Line(circle=(cx, cy, r), width=1.4)
            else:
                Line(rounded_rectangle=(x, y, w, h, r), width=1.4)
        with self.canvas.after:
            Color(1, 1, 1, 0.95)
            s = r * 0.42
            if self.icone == 'seta':
                Line(points=[cx - s, cy - s * 0.15, cx, cy + s * 0.75, cx + s, cy - s * 0.15], width=3.4,
                     cap='round', joint='round')
                Line(points=[cx, cy + s * 0.70, cx, cy - s * 0.85], width=3.4, cap='round')
            elif self.icone == 'seta_baixo':
                Line(points=[cx - s, cy + s * 0.15, cx, cy - s * 0.75, cx + s, cy + s * 0.15], width=3.4,
                     cap='round', joint='round')
                Line(points=[cx, cy - s * 0.70, cx, cy + s * 0.85], width=3.4, cap='round')
            elif self.icone in ('casa', 'arvore', 'caverna', 'janela'):
                _arte(self.icone, cx, y + h * 0.68, h * 0.17)
            elif self.icone == 'camera':
                Line(rounded_rectangle=(cx - s * 1.0, cy - s * 0.65, s * 2.0, s * 1.3, s * 0.2), width=2.4)
                Line(circle=(cx, cy - s * 0.02, s * 0.38), width=2.2)
                Line(points=[cx - s * 0.45, cy + s * 0.65, cx - s * 0.25, cy + s * 0.95, cx + s * 0.25, cy + s * 0.95,
                             cx + s * 0.45, cy + s * 0.65], width=2.2, joint='round')
            elif self.icone == 'mochila':
                Line(rounded_rectangle=(cx - s * 0.85, cy - s * 0.95, s * 1.7, s * 1.7, s * 0.45), width=2.4)
                Line(points=[cx - s * 0.5, cy + s * 0.75, cx - s * 0.4, cy + s * 1.15, cx + s * 0.4, cy + s * 1.15,
                             cx + s * 0.5, cy + s * 0.75], width=2.2, joint='round')
                Line(rounded_rectangle=(cx - s * 0.5, cy - s * 0.65, s * 1.0, s * 0.6, s * 0.15), width=2.0)
            elif self.icone == 'menu':
                for dy in (-s * 0.55, 0, s * 0.55):
                    Line(points=[cx - s * 0.8, cy + dy, cx + s * 0.8, cy + dy], width=2.6, cap='round')
        if self.icone in ('casa', 'arvore', 'caverna', 'janela'):
            self.rotulo.pos = (x, y)
            self.rotulo.size = (w, h * 0.42)
        else:
            self.rotulo.pos = self.pos
            self.rotulo.size = self.size
        self.rotulo.text_size = self.rotulo.size

    def _forma(self, x, y, w, h, r):
        if self.forma == 'circulo':
            Ellipse(pos=(x, y), size=(w, h))
        else:
            RoundedRectangle(pos=(x, y), size=(w, h), radius=[r])

    def on_touch_down(self, touch):
        if not self.collide_point(*touch.pos):
            return False
        self._uid = touch.uid
        self.apertado = True
        self.redesenhar()
        if self.imediato and self.ao_tocar:
            self.ao_tocar()
            if self.repetir > 0:                       # segurando o botão, repete a ação
                self._parar_rep()
                self._rep = Clock.schedule_interval(self._repetir, self.repetir)
        return True

    def _repetir(self, dt):
        if self._uid is None or self.disabled or self.opacity < 0.5:
            self._parar_rep()
            return False
        if self.ao_tocar:
            self.ao_tocar()

    def _parar_rep(self):
        if self._rep is not None:
            self._rep.cancel()
            self._rep = None

    def on_touch_up(self, touch):
        if touch.uid != self._uid:
            return False
        self._uid = None
        self._parar_rep()
        self.apertado = False
        self.redesenhar()
        if not self.imediato and self.collide_point(*touch.pos) and self.ao_tocar:
            self.ao_tocar()
        return True


class Deslizante(Widget):
    """Controle deslizante simples, todo branco/cinza."""

    def __init__(self, minimo, maximo, valor, ao_mudar, **kw):
        kw.setdefault('size_hint', (None, None))
        super().__init__(**kw)
        self.minimo, self.maximo, self.valor, self.ao_mudar = minimo, maximo, valor, ao_mudar
        self._uid = None
        self.bind(pos=self.redesenhar, size=self.redesenhar)
        self.redesenhar()

    def redesenhar(self, *args):
        x, y = self.pos
        w, h = self.size
        d = h * 0.72
        frac = (self.valor - self.minimo) / float(self.maximo - self.minimo)
        px = x + d / 2 + frac * (w - d)
        self.canvas.clear()
        with self.canvas:
            Color(1, 1, 1, 0.20)
            RoundedRectangle(pos=(x, y + h * 0.42), size=(w, h * 0.16), radius=[h * 0.08])
            Color(1, 1, 1, 0.75)
            RoundedRectangle(pos=(x, y + h * 0.42), size=(max(1.0, px - x), h * 0.16), radius=[h * 0.08])
            Color(1, 1, 1, 1)
            Ellipse(pos=(px - d / 2, y + (h - d) / 2), size=(d, d))

    def _mudar(self, tx):
        d = self.height * 0.72
        frac = (tx - self.x - d / 2) / max(1.0, (self.width - d))
        frac = max(0.0, min(1.0, frac))
        self.valor = self.minimo + frac * (self.maximo - self.minimo)
        self.redesenhar()
        if self.ao_mudar:
            self.ao_mudar(self.valor)

    def on_touch_down(self, touch):
        if not self.collide_point(*touch.pos):
            return False
        self._uid = touch.uid
        self._mudar(touch.x)
        return True

    def on_touch_move(self, touch):
        if touch.uid != self._uid:
            return False
        self._mudar(touch.x)
        return True

    def on_touch_up(self, touch):
        if touch.uid != self._uid:
            return False
        self._uid = None
        return True


class Menu(FloatLayout):
    NOMES = (('casa', 'Casa', 'dentro e quintal', 'casa'),
             ('aberto', 'Mundo aberto', 'floresta e campo', 'arvore'),
             ('fechado', 'Casa fechada', 'janelas, sem saída', 'janela'))
    DOURADO = (1.0, 0.85, 0.42)
    NOME_JOGO = 'JOGO DE SAMUEL'
    OPCOES = (
        ('Qualidade', 'q_modo', ['auto', 'baixa', 'media', 'alta'], ['Automática', 'Baixa', 'Média', 'Alta']),
        ('Distância', 'dist_mult', [0.6, 0.8, 1.0, 1.25], ['Curta', 'Média', 'Longa', 'Máxima']),
        ('Texturas', 'texturas', [True, False], ['Ligadas', 'Desligadas']),
        ('Detalhe da textura', 'detalhe', [0, 1, 2], ['Normal', 'Alto', 'Máximo']),
        ('Nuvens', 'nuvens_on', [True, False], ['Sim', 'Não']),
        ('Música', 'musica_nivel', ['desl', 'baixa', 'media', 'alta'], ['Desligada', 'Baixa', 'Média', 'Alta']),
        ('Sons', 'sfx_nivel', ['desl', 'baixa', 'media', 'alta'], ['Desligados', 'Baixos', 'Médios', 'Altos']),
        ('Cena de entrada', 'cena_on', [True, False], ['Sim', 'Não']),
        ('Mostrar FPS', 'fps_on', [False, True], ['Não', 'Sim']),
        ('Câmera', 'camera', ['primeira', 'terceira', 'segunda'], ['1ª pessoa', '3ª pessoa', '2ª pessoa']),
    )

    def __init__(self, app, **kw):
        super().__init__(**kw)
        self.app = app
        self.modo = 'inicio'
        self.anterior = 'inicio'
        nh = dict(size_hint=(None, None))
        self.titulo = Label(text=self.NOME_JOGO, font_size='32sp', bold=True, color=self.DOURADO + (1,), **nh)
        self.sub = Label(text='Escolha um mapa', font_size='15sp', color=(1, 1, 1, 0.70), **nh)
        self.mapas = []
        for chave, nome, desc, ic in self.NOMES:
            b = Botao(texto=f"{nome}\n[size=12sp]{desc}[/size]", icone=ic, fonte='16sp',
                      ao_tocar=lambda c=chave: app.escolher(c))
            b.rotulo.markup = True
            self.mapas.append((chave, b))
        self.lbl_sens = Label(text='Sensibilidade do olhar', font_size='14sp', color=(1, 1, 1, 0.75), **nh)
        self.slider = Deslizante(0.08, 0.60, app.cena.sens, lambda v: setattr(app.cena, 'sens', v))
        self.btn_cont = Botao(texto='Continuar', fonte='18sp', ao_tocar=app.fechar_menu)
        self.btn_menu = Botao(texto='Sair para o menu', fonte='18sp', ao_tocar=app.sair_para_menu)
        self.btn_cfg = Botao(texto='Configurações', fonte='18sp', ao_tocar=lambda: app.abrir_menu('config'))
        self.btn_sair = Botao(texto='Sair do jogo', fonte='18sp', ao_tocar=lambda: App.get_running_app().stop())
        self.btn_rede = Botao(texto='Multijogador', fonte='18sp', ao_tocar=lambda: app.abrir_menu('rede'))
        self.lbl_ip = Label(text='', font_size='14sp', color=(1, 1, 1, 0.80), **nh)
        self.entrada = TextInput(hint_text='IP do anfitrião (vazio = procurar sala sozinho)', multiline=False,
                                 font_size='16sp', size_hint=(None, None), write_tab=False,
                                 background_color=(0.12, 0.15, 0.14, 1), foreground_color=(1, 1, 1, 1),
                                 hint_text_color=(1, 1, 1, 0.45), cursor_color=(1, 0.85, 0.42, 1), padding=[14, 12, 14, 12])
        self.btn_criar = Botao(texto='Criar sala', fonte='18sp', ao_tocar=self.criar_sala)
        self.btn_entrar = Botao(texto='Entrar na sala', fonte='18sp', ao_tocar=self.entrar_sala)
        self.btn_desc = Botao(texto='Desconectar', fonte='18sp', ao_tocar=self.desconectar)
        self.btn_voltar = Botao(texto='Voltar', fonte='18sp', ao_tocar=lambda: app.abrir_menu(self.anterior))
        self.btn_mundos = Botao(texto='Meus mundos', fonte='17sp', ao_tocar=lambda: app.abrir_menu('mundos'))
        self.btn_novo = Botao(texto='Novo mundo', fonte='17sp', ao_tocar=lambda: app.abrir_menu('novo'))
        self.btn_apagar = Botao(texto='Apagar mundo', fonte='17sp', ao_tocar=self.alternar_apagar)
        self.btn_voltar_m = Botao(texto='Voltar', fonte='17sp', ao_tocar=lambda: app.abrir_menu('inicio'))
        self.btn_voltar_n = Botao(texto='Voltar', fonte='15sp', ao_tocar=lambda: app.abrir_menu('mundos'))
        self.btn_criar_m = Botao(texto='Criar e jogar', fonte='15sp', ao_tocar=self.criar_mundo)
        self.btn_voltar_i = Botao(texto='Continuar', fonte='17sp', ao_tocar=app.fechar_menu)
        self.inv_slots = [Botao(texto='', fonte='15sp', ao_tocar=lambda i=i: self.tocar_inv(i)) for i in range(8)]
        for b in self.inv_slots:
            b.rotulo.markup = True
        self.btn_add_i = Botao(texto='Adicionar itens: Não', fonte='15sp', ao_tocar=self.alternar_add)
        self.add_modo = False
        self.pf = dict(PERFIL or perfil_padrao('m'))
        self.pf_edicao = False
        self.nome_perfil = TextInput(text=self.pf['nome'], multiline=False, font_size='17sp', size_hint=(None, None),
                                     write_tab=False, background_color=(0.12, 0.15, 0.14, 1), foreground_color=(1, 1, 1, 1),
                                     cursor_color=(1, 0.85, 0.42, 1), padding=[14, 12, 14, 12], halign='center')
        self.btn_menino = Botao(texto='Menino', fonte='17sp', ao_tocar=lambda: self.escolher_sexo('m'))
        self.btn_menina = Botao(texto='Menina', fonte='17sp', ao_tocar=lambda: self.escolher_sexo('f'))
        self.pf_btn = [Botao(texto='', fonte='14sp', ao_tocar=lambda i=i: self.alternar_pf(i)) for i in range(6)]
        self.btn_ok_p = Botao(texto='Começar', fonte='17sp', ao_tocar=self.confirmar_perfil)
        self.btn_voltar_p = Botao(texto='Voltar', fonte='17sp', ao_tocar=lambda: app.abrir_menu('config'))
        self.btn_perfil_cfg = Botao(texto='Personagem', fonte='15sp', ao_tocar=lambda: app.abrir_menu('perfil', edicao=True))
        self.btn_cheats_cfg = Botao(texto='Cheats', fonte='15sp', ao_tocar=lambda: app.abrir_menu('cheats'))
        self.btn_ck = Botao(texto='', fonte='15sp', ao_tocar=self.tocar_ativar_cheats)
        self.ch_btns = [Botao(texto='', fonte='14sp', ao_tocar=lambda i=i: self.tocar_cheat(i)) for i in range(len(CHEATS_G))]
        self.btn_voltar_c = Botao(texto='Voltar', fonte='17sp', ao_tocar=lambda: app.abrir_menu('config'))
        self.ck_confirma = False
        self.apagando = False
        self.slots = []
        for i in range(MAX_MUNDOS):
            b = Botao(texto='', fonte='16sp', ao_tocar=lambda i=i: self.tocar_mundo(i))
            b.rotulo.markup = True
            self.slots.append(b)
        self.nome_mundo = TextInput(text='Meu mundo', multiline=False, font_size='17sp', size_hint=(None, None),
                                    write_tab=False, background_color=(0.12, 0.15, 0.14, 1),
                                    foreground_color=(1, 1, 1, 1), cursor_color=(1, 0.85, 0.42, 1),
                                    padding=[14, 12, 14, 12], halign='center')
        self.novo = {'tipo': 0, 'dens': 1, 'gemas': 1, 'cheats': {}}
        self.nov = []
        for i in range(3 + len(CHEATS)):
            self.nov.append(Botao(texto='', fonte='14sp', ao_tocar=lambda i=i: self.alternar_novo(i)))
        self.cfg = []
        for i, op in enumerate(self.OPCOES):
            b = Botao(texto='', fonte='15sp', ao_tocar=lambda i=i: self.alternar(i))
            self.cfg.append(b)
        self.todos = [self.titulo, self.sub, self.lbl_sens, self.slider, self.btn_cont, self.btn_menu,
                      self.btn_cfg, self.btn_sair, self.btn_voltar, self.btn_rede, self.lbl_ip, self.entrada,
                      self.btn_criar, self.btn_entrar, self.btn_desc] + [b for _, b in self.mapas] + self.cfg + \
                     [self.btn_mundos, self.btn_novo, self.btn_apagar, self.btn_voltar_m, self.btn_voltar_n, self.btn_voltar_i, self.btn_add_i] + self.inv_slots + \
                     [
                      self.btn_criar_m, self.nome_mundo, self.nome_perfil, self.btn_menino, self.btn_menina, self.btn_ok_p,
                      self.btn_voltar_p, self.btn_perfil_cfg, self.btn_cheats_cfg, self.btn_ck, self.btn_voltar_c] + self.ch_btns + self.pf_btn + self.slots + self.nov
        for wd in self.todos:
            self.add_widget(wd)
        self.bind(size=self.organizar, pos=self.organizar)

    def _mostrar(self, wd, sim):
        wd.opacity = 1.0 if sim else 0.0
        wd.disabled = not sim
        if sim and wd.parent is None:
            self.add_widget(wd)
        elif not sim and wd.parent is not None:
            self.remove_widget(wd)

    # ---------- mundos ----------
    def alternar_add(self):
        self.add_modo = not self.add_modo
        self.atualizar_inv()

    def tocar_inv(self, i):
        c = self.app.cena
        if i >= len(ITENS):
            return
        k = ITENS[i][0]
        if self.add_modo and c.cheats.get('itens'):
            c.dar(k, 1)
        else:
            c.equipar(k)
        self.atualizar_inv()

    def atualizar_inv(self):
        c = self.app.cena
        tem_cheat = bool(c.cheats.get('itens'))
        if not tem_cheat:
            self.add_modo = False
        self._mostrar(self.btn_add_i, self.modo == 'inventario' and tem_cheat)
        self.btn_add_i.rotulo.text = 'Adicionar itens: ' + ('Sim' if self.add_modo else 'Não')
        self.btn_add_i.ativo = self.add_modo
        self.btn_add_i.redesenhar()
        self.sub.text = 'Toque num item para adicionar' if self.add_modo else 'Toque num item para segurar na mão'
        for n, b in enumerate(self.inv_slots):
            if n >= len(ITENS):
                b.rotulo.text = '[color=777777]vazio[/color]'
                b.ativo = False
            else:
                k, nome = ITENS[n]
                q = c.inv.get(k, 0)
                if k == 'machado' and c.cheats.get('machado') and q == 0:
                    q = 1
                extra = '\n[size=11sp]na mão[/size]' if c.mao == k else ''
                b.rotulo.text = f'{nome}\n[size=20sp]{q}[/size]{extra}'
                b.ativo = (c.mao == k) or (q > 0 and False)
            b.redesenhar()

    # ---------- perfil do personagem ----------
    PF_OPCOES = (('Pele', 'pele', ROT_PELE), ('Cabelo', 'cabelo', ROT_CABELO), ('Penteado', 'estilo', None),
                 ('Roupa', 'roupa', ROT_ROUPA), ('Calça/Saia', 'calca', ROT_CALCA), ('Olhos', 'olho', ROT_OLHO))

    def escolher_sexo(self, s):
        if self.pf['sexo'] == s:
            return
        self.pf['sexo'] = s
        self.pf['estilo'] = 0
        self.atualizar_pf()

    def alternar_pf(self, i):
        nome, chave, rots = self.PF_OPCOES[i]
        n = len(rots) if rots else len(ESTILOS_CAB[self.pf['sexo']])
        self.pf[chave] = (self.pf[chave] + 1) % n
        self.atualizar_pf()

    def atualizar_pf(self):
        p = self.pf
        p['nome'] = (self.nome_perfil.text or '').strip()[:16] or 'Jogador'
        self.btn_menino.ativo = (p['sexo'] == 'm')
        self.btn_menina.ativo = (p['sexo'] == 'f')
        self.btn_menino.redesenhar()
        self.btn_menina.redesenhar()
        self.btn_menino.rotulo.text = 'Menino'
        self.btn_menina.rotulo.text = 'Menina'
        for b, (nome, chave, rots) in zip(self.pf_btn, self.PF_OPCOES):
            rr = rots if rots else ESTILOS_CAB[p['sexo']]
            b.rotulo.text = f"{nome}: {rr[p[chave] % len(rr)]}"
        self.app.cena.aplicar_perfil(p)

    def confirmar_perfil(self):
        self.atualizar_pf()
        salvar_perfil(self.pf)
        self.app.cena.vitrine = False
        self.app.abrir_menu('config' if self.pf_edicao else 'inicio')

    def alternar_apagar(self):
        self.apagando = not self.apagando
        self.atualizar_mundos()

    def atualizar_mundos(self):
        self.btn_apagar.rotulo.text = 'Apagando: toque num mundo' if self.apagando else 'Apagar mundo'
        self.btn_apagar.ativo = self.apagando
        self.btn_apagar.redesenhar()
        self.sub.text = 'Toque no mundo que quer APAGAR' if self.apagando else (
            'Toque num mundo para jogar' if MUNDOS else 'Você ainda não criou nenhum mundo')
        for i, b in enumerate(self.slots):
            if i < len(MUNDOS):
                m = MUNDOS[i]
                b.rotulo.text = f"{m['nome'][:22]}\n[size=12sp]{descricao_mundo(m)}[/size]"
                self._mostrar(b, self.modo == 'mundos')
            else:
                self._mostrar(b, False)
        self._mostrar(self.btn_novo, self.modo == 'mundos' and len(MUNDOS) < MAX_MUNDOS)
        self.organizar()

    def tocar_mundo(self, i):
        if i >= len(MUNDOS):
            return
        if self.apagando:
            del MUNDOS[i]
            salvar_mundos()
            self.apagando = False
            self.atualizar_mundos()
        else:
            self.app.escolher_mundo(MUNDOS[i])

    def alternar_novo(self, i):
        n = self.novo
        if i == 0:
            n['tipo'] = (n['tipo'] + 1) % len(TIPOS_MUNDO)
        elif i == 1:
            n['dens'] = (n['dens'] + 1) % len(DENS_MUNDO)
        elif i == 2:
            n['gemas'] = (n['gemas'] + 1) % len(GEMAS_MUNDO)
        else:
            k = CHEATS[i - 3][0]
            n['cheats'][k] = not n['cheats'][k]
        self.atualizar_novo()

    def atualizar_novo(self):
        n = self.novo
        t = [f"Tipo: {ROT_TIPOS[n['tipo']]}", f"Árvores: {ROT_DENS[n['dens']]}", f"{ROT_GEMAS[n['gemas']]}"]
        t += [f"{r}: {'Sim' if n['cheats'][k] else 'Não'}" for k, r in CHEATS]
        for b, tx in zip(self.nov, t):
            b.rotulo.text = tx
        for b, k in zip(self.nov[3:], [k for k, _ in CHEATS]):
            b.ativo = n['cheats'][k]
            b.redesenhar()

    def criar_mundo(self):
        n = self.novo
        m = novo_mundo(self.nome_mundo.text, TIPOS_MUNDO[n['tipo']], DENS_MUNDO[n['dens']], GEMAS_MUNDO[n['gemas']],
                       n['cheats'])
        if len(MUNDOS) >= MAX_MUNDOS:
            return
        MUNDOS.append(m)
        salvar_mundos()
        self.app.escolher_mundo(m)

    def criar_sala(self):
        self.app.cena.rede.criar()
        self.preparar('rede', 'MULTIJOGADOR')

    def entrar_sala(self):
        self.app.cena.rede.entrar(self.entrada.text)
        self.preparar('rede', 'MULTIJOGADOR')

    def desconectar(self):
        self.app.cena.rede.parar()
        self.preparar('rede', 'MULTIJOGADOR')

    def tick(self, dt):
        c = self.app.cena
        c.musica.nivel = c.musica_nivel
        c.sfx.nivel = c.sfx_nivel
        c.musica.tick()
        if self.modo == 'rede':
            r = self.app.cena.rede
            self.sub.text = r.status
            n = len(r.jogadores())
            self.lbl_ip.text = 'Seu IP: %s    |    Jogadores na sala: %d' % (ip_local(), (1 + n) if r.rodando else 0)
            ativo = r.rodando
            for wd, sim in ((self.btn_criar, not ativo), (self.btn_entrar, not ativo), (self.entrada, not ativo),
                            (self.btn_desc, ativo)):
                if (wd.parent is not None) != sim:
                    self._mostrar(wd, sim)
            self.organizar()

    def tocar_ativar_cheats(self):
        if CONFIG['cheats_ok']:
            CONFIG['cheats_ok'] = False
            self.ck_confirma = False
        elif not self.ck_confirma:
            self.ck_confirma = True
        else:
            CONFIG['cheats_ok'] = True
            self.ck_confirma = False
        salvar_cfg()
        self.atualizar_cheats()

    def tocar_cheat(self, i):
        if not CONFIG['cheats_ok']:
            return
        k = CHEATS_G[i][0]
        CONFIG['cheats'][k] = not CONFIG['cheats'].get(k, False)
        salvar_cfg()
        self.atualizar_cheats()

    def atualizar_cheats(self):
        ok = CONFIG['cheats_ok']
        if ok:
            self.btn_ck.rotulo.text = 'Cheats ATIVADOS (toque para desativar)'
        elif self.ck_confirma:
            self.btn_ck.rotulo.text = 'Ativar cheats, certeza? Toque de novo'
        else:
            self.btn_ck.rotulo.text = 'Ativar cheats'
        self.btn_ck.ativo = ok or self.ck_confirma
        self.btn_ck.redesenhar()
        self.sub.text = 'Cheats são para brincar; ative e escolha abaixo.'
        for b, (k, r) in zip(self.ch_btns, CHEATS_G):
            on = bool(CONFIG['cheats'].get(k))
            b.rotulo.text = f"{r}: {'Sim' if on else 'Não'}" if ok else f"{r} (bloqueado)"
            b.ativo = ok and on
            b.opacity = 1.0 if ok else 0.45
            b.redesenhar()

    def alternar(self, i):
        nome, attr, vals, rots = self.OPCOES[i]
        atual = getattr(self.app.cena, attr)
        k = vals.index(atual) if atual in vals else 0
        setattr(self.app.cena, attr, vals[(k + 1) % len(vals)])
        CONFIG['opcoes'][attr] = getattr(self.app.cena, attr)
        salvar_cfg()
        self.atualizar_cfg()

    def atualizar_cfg(self):
        for b, (nome, attr, vals, rots) in zip(self.cfg, self.OPCOES):
            atual = getattr(self.app.cena, attr)
            k = vals.index(atual) if atual in vals else 0
            b.rotulo.text = f"{nome}: {rots[k]}"

    def preparar(self, modo, titulo, edicao=False):
        self.pf_edicao = bool(edicao)
        self.app.cena.vitrine = (modo == 'perfil')
        if modo == 'perfil':
            self.app.cena.intro = False
            self.pf = dict(PERFIL or perfil_padrao('m'))
            self.nome_perfil.text = self.pf['nome']
            self.btn_ok_p.rotulo.text = 'Salvar' if edicao else 'Começar'
        if modo in ('config', 'rede') and self.modo not in ('config', 'rede'):
            self.anterior = self.modo
        self.modo = modo
        if modo == 'cheats':
            self.ck_confirma = False
            self.atualizar_cheats()
        self.titulo.text = titulo
        nome = {c: n for c, n, _, _ in self.NOMES}.get(self.app.cena.chave, '')
        if self.app.cena.mundo is not None:
            nome = self.app.cena.mundo['nome']
        self.sub.text = ('Mapa: ' + nome) if modo == 'pausa' else 'Escolha um mapa'
        if modo == 'cheats':
            self.sub.text = 'Só para brincar: ative e escolha abaixo'
        if modo == 'novo':
            self.sub.text = 'Dê um nome e escolha como será o mundo'
        self.apagando = False
        visiveis = {
            'inicio': [self.titulo, self.sub, self.lbl_sens, self.slider, self.btn_cfg, self.btn_sair, self.btn_rede,
                       self.btn_mundos] +
                      [b for _, b in self.mapas],
            'pausa': [self.titulo, self.sub, self.lbl_sens, self.slider, self.btn_cont, self.btn_cfg, self.btn_menu],
            'config': [self.titulo, self.btn_voltar, self.btn_perfil_cfg, self.btn_cheats_cfg] + self.cfg,
            'cheats': [self.titulo, self.sub, self.btn_ck, self.btn_voltar_c] + self.ch_btns,
            'perfil': [self.titulo, self.sub, self.nome_perfil, self.btn_menino, self.btn_menina, self.btn_ok_p] + self.pf_btn +
                      ([self.btn_voltar_p] if self.pf_edicao else []),
            'inventario': [self.titulo, self.sub, self.btn_voltar_i, self.btn_add_i] + self.inv_slots,
            'mundos': [self.titulo, self.sub, self.btn_voltar_m, self.btn_novo, self.btn_apagar] + self.slots,
            'novo': [self.titulo, self.sub, self.nome_mundo, self.btn_voltar_n, self.btn_criar_m] + self.nov,
            'rede': [self.titulo, self.sub, self.lbl_ip, self.btn_voltar, self.btn_criar, self.btn_entrar, self.entrada],
        }[modo]
        for wd in self.todos:
            self._mostrar(wd, wd in visiveis)
        for chave, b in self.mapas:
            b.ativo = (chave == self.app.cena.chave and self.app.cena.mundo is None)
            b.redesenhar()
        self.slider.valor = self.app.cena.sens
        self.slider.redesenhar()
        self.atualizar_cfg()
        if modo == 'perfil':
            self.sub.text = 'Escolha como você é (dá pra mudar depois)' if not edicao else 'Mude sua aparência'
            self.atualizar_pf()
        if modo == 'inventario':
            self.atualizar_inv()
        if modo == 'mundos':
            self.atualizar_mundos()
        if modo == 'novo':
            self.atualizar_novo()
        self.tick(0)
        self.organizar()

    def _fundo(self, W, H, x0, y0, cw, ch):
        # céu noturno em faixas verde-escuro (sem azul/vermelho), estrelas e gemas flutuando
        n = 14
        for i in range(n):
            t = i / float(n - 1)
            Color(0.05 + 0.05 * t, 0.10 + 0.07 * (1 - t) + 0.02 * t, 0.10 + 0.04 * (1 - t), 1)
            Rectangle(pos=(0, H * (1 - (i + 1) / float(n))), size=(W, H / float(n) + 1))
        Color(1, 1, 1, 0.45)
        for k in range(46):
            sx = ((k * 7919) % 1000) / 1000.0 * W
            sy = ((k * 104729) % 1000) / 1000.0 * H
            r = 1.0 + (k % 3)
            Ellipse(pos=(sx, sy), size=(r, r))
        # colinas
        Color(0.04, 0.12, 0.08, 1)
        Ellipse(pos=(-W * 0.2, -H * 0.55), size=(W * 0.8, H * 0.75))
        Color(0.05, 0.15, 0.10, 1)
        Ellipse(pos=(W * 0.35, -H * 0.60), size=(W * 0.95, H * 0.80))
        # gemas flutuando
        for k, (fx, fy, fu) in enumerate(((0.07, 0.78, 0.035), (0.93, 0.70, 0.045), (0.05, 0.25, 0.03),
                                           (0.95, 0.22, 0.035), (0.12, 0.50, 0.022), (0.88, 0.48, 0.025))):
            u = H * fu
            cx, cy = W * fx, H * fy
            Color(1, 0.84, 0.30, 0.55)
            _poli([(cx, cy - u * 1.3), (cx + u, cy), (cx, cy + u * 1.3), (cx - u, cy)])
            Color(1, 1, 1, 0.35)
            _poli([(cx, cy + u * 1.3), (cx - u, cy), (cx - u * 0.1, cy + u * 0.2), (cx, cy + u * 0.9)])
        # painel
        Color(0, 0, 0, 0.30)
        RoundedRectangle(pos=(x0 + 3, y0 - 5), size=(cw, ch), radius=[ch * 0.06])
        Color(0.07, 0.10, 0.09, 0.92)
        RoundedRectangle(pos=(x0, y0), size=(cw, ch), radius=[ch * 0.06])
        Color(1.0, 0.85, 0.42, 0.16)
        RoundedRectangle(pos=(x0, y0 + ch * 0.74), size=(cw, ch * 0.26), radius=[ch * 0.06, ch * 0.06, 0, 0])
        Color(1.0, 0.85, 0.42, 0.75)
        Line(rounded_rectangle=(x0, y0, cw, ch, ch * 0.06), width=1.6)
        Color(1.0, 0.85, 0.42, 0.30)
        Line(rounded_rectangle=(x0 + 6, y0 + 6, cw - 12, ch - 12, ch * 0.05), width=1.0)

    def organizar(self, *args):
        W, H = self.size
        if W < 10 or H < 10:
            return
        modo = self.modo
        pausa = (modo == 'pausa')
        if modo == 'perfil':
            cw, ch = min(W * 0.58, H * 1.25), H * 0.92
        elif pausa:
            cw, ch = min(W * 0.62, H * 1.15), H * 0.90
        elif modo == 'config':
            cw, ch = min(W * 0.90, H * 1.85), H * 0.92
        else:
            cw, ch = min(W * 0.90, H * 1.85), H * 0.92
        x0, y0 = (W - cw) / 2.0, (H - ch) / 2.0
        if modo == 'perfil':
            x0 = W * 0.02
        self.canvas.before.clear()
        with self.canvas.before:
            if modo == 'perfil':
                Color(0, 0, 0, 0.30)
                RoundedRectangle(pos=(x0 + 3, y0 - 5), size=(cw, ch), radius=[ch * 0.06])
                Color(0.07, 0.10, 0.09, 0.90)
                RoundedRectangle(pos=(x0, y0), size=(cw, ch), radius=[ch * 0.06])
                Color(1.0, 0.85, 0.42, 0.75)
                Line(rounded_rectangle=(x0, y0, cw, ch, ch * 0.06), width=1.6)
            else:
                self._fundo(W, H, x0, y0, cw, ch)
            u = ch * 0.035
            cy = y0 + ch * 0.87
            Color(1.0, 0.85, 0.42, 1)
            dx = 0.22 if pausa else 0.17
            for cx in (x0 + cw * dx, x0 + cw * (1 - dx)):
                _poli([(cx, cy - u * 1.4), (cx + u, cy), (cx, cy + u * 1.4), (cx - u, cy)])
            Color(1.0, 0.85, 0.42, 0.40)
            Line(points=[x0 + cw * 0.1, y0 + ch * 0.73, x0 + cw * 0.9, y0 + ch * 0.73], width=1.2)
        self.titulo.size = (cw, ch * 0.16)
        self.titulo.pos = (x0, y0 + ch * 0.79)
        self.sub.size = (cw, ch * 0.08)
        self.sub.pos = (x0, y0 + ch * 0.65)
        gap = cw * 0.025
        if modo == 'perfil':
            self.sub.pos = (x0, y0 + ch * 0.66)
            self.nome_perfil.size = (cw * 0.84, ch * 0.085)
            self.nome_perfil.pos = (x0 + cw * 0.08, y0 + ch * 0.575)
            bwx = cw * 0.41
            for k, b in enumerate((self.btn_menino, self.btn_menina)):
                b.size = (bwx, ch * 0.10)
                b.pos = (x0 + cw * 0.08 + k * (bwx + cw * 0.02), y0 + ch * 0.455)
            for k, b in enumerate(self.pf_btn):
                lin, col = k // 2, k % 2
                b.size = (bwx, ch * 0.092)
                b.pos = (x0 + cw * 0.08 + col * (bwx + cw * 0.02), y0 + ch * (0.340 - 0.108 * lin))
            if self.pf_edicao:
                self.btn_ok_p.size = self.btn_voltar_p.size = (bwx, ch * 0.095)
                self.btn_ok_p.pos = (x0 + cw * 0.08 + bwx + cw * 0.02, y0 + ch * 0.02)
                self.btn_voltar_p.pos = (x0 + cw * 0.08, y0 + ch * 0.02)
            else:
                self.btn_ok_p.size = (cw * 0.84, ch * 0.095)
                self.btn_ok_p.pos = (x0 + cw * 0.08, y0 + ch * 0.02)
        elif modo == 'config':
            bw, bh = cw * 0.30, ch * 0.105
            slots = self.cfg + [self.btn_perfil_cfg, self.btn_cheats_cfg, self.btn_voltar]
            for k, b in enumerate(slots):
                lin, col = k // 3, k % 3
                b.size = (bw, bh)
                b.pos = (x0 + cw * 0.5 - bw * 1.5 - gap + col * (bw + gap), y0 + ch * (0.60 - 0.125 * lin))
        elif modo == 'cheats':
            self.sub.pos = (x0, y0 + ch * 0.66)
            self.btn_ck.size = (cw * 0.60, ch * 0.11)
            self.btn_ck.pos = (x0 + cw * 0.20, y0 + ch * 0.54)
            bw4 = (cw * 0.94 - 3 * gap) / 4.0
            for k, b in enumerate(self.ch_btns + [self.btn_voltar_c]):
                lin, col = k // 4, k % 4
                b.size = (bw4, ch * 0.11)
                b.pos = (x0 + cw * 0.03 + col * (bw4 + gap), y0 + ch * (0.38 - 0.14 * lin))
        elif modo == 'inventario':
            bw, bh = (cw * 0.94 - 3 * gap) / 4.0, ch * 0.15
            for k, b in enumerate(self.inv_slots):
                lin, col = k // 4, k % 4
                b.size = (bw, bh)
                b.pos = (x0 + cw * 0.03 + col * (bw + gap), y0 + ch * (0.49 - 0.18 * lin))
            self.btn_voltar_i.size = (cw * 0.30, ch * 0.11)
            self.btn_add_i.size = (cw * 0.34, ch * 0.11)
            self.btn_voltar_i.pos = (x0 + cw * 0.18, y0 + ch * 0.07)
            self.btn_add_i.pos = (x0 + cw * 0.52, y0 + ch * 0.07)
        elif modo == 'mundos':
            bw, bh = cw * 0.42, ch * 0.115
            for k, b in enumerate(self.slots):
                lin, col = k // 2, k % 2
                b.size = (bw, bh)
                b.pos = (x0 + cw * 0.5 + (gap / 2 if col else -gap / 2 - bw), y0 + ch * (0.52 - 0.13 * lin))
            bw3 = cw * 0.29
            for k, b in enumerate((self.btn_novo, self.btn_apagar, self.btn_voltar_m)):
                b.size = (bw3, ch * 0.11)
                b.pos = (x0 + cw / 2 - bw3 * 1.5 - gap + k * (bw3 + gap), y0 + ch * 0.07)
        elif modo == 'novo':
            self.sub.pos = (x0, y0 + ch * 0.64)
            self.nome_mundo.size = (cw * 0.62, ch * 0.09)
            self.nome_mundo.pos = (x0 + cw * 0.19, y0 + ch * 0.55)
            bw4 = (cw * 0.94 - 3 * gap) / 4.0
            botoes = self.nov + [self.btn_criar_m, self.btn_voltar_n]
            for k, b in enumerate(botoes):
                lin, col = k // 4, k % 4
                b.size = (bw4, ch * 0.10)
                b.pos = (x0 + cw * 0.03 + col * (bw4 + gap), y0 + ch * (0.425 - 0.118 * lin))
        elif modo == 'rede':
            self.sub.pos = (x0, y0 + ch * 0.63)
            self.lbl_ip.size = (cw, ch * 0.07)
            self.lbl_ip.pos = (x0, y0 + ch * 0.55)
            self.entrada.size = (cw * 0.62, ch * 0.12)
            self.entrada.pos = (x0 + cw * 0.19, y0 + ch * 0.40)
            bw2, bh = cw * 0.34, ch * 0.115
            self.btn_criar.size = self.btn_entrar.size = self.btn_desc.size = (bw2, bh)
            self.btn_criar.pos = (x0 + cw / 2 - bw2 - gap / 2, y0 + ch * 0.24)
            self.btn_entrar.pos = (x0 + cw / 2 + gap / 2, y0 + ch * 0.24)
            self.btn_desc.pos = (x0 + (cw - bw2) / 2, y0 + ch * 0.24)
            self.btn_voltar.size = (bw2, bh)
            self.btn_voltar.pos = (x0 + (cw - bw2) / 2, y0 + ch * 0.07)
        elif pausa:
            bw2, bh = cw * 0.70, ch * 0.115
            for k, b in enumerate((self.btn_cont, self.btn_cfg, self.btn_menu)):
                b.size = (bw2, bh)
                b.pos = (x0 + (cw - bw2) / 2, y0 + ch * (0.50 - 0.14 * k))
            self.lbl_sens.size = (cw, ch * 0.07)
            self.lbl_sens.pos = (x0, y0 + ch * 0.15)
            self.slider.size = (cw * 0.70, ch * 0.08)
            self.slider.pos = (x0 + cw * 0.15, y0 + ch * 0.06)
        else:
            bw = (cw * 0.90 - 2 * gap) / 3.0
            for i, (_, b) in enumerate(self.mapas):
                b.size = (bw, ch * 0.37)
                b.pos = (x0 + cw * 0.05 + i * (bw + gap), y0 + ch * 0.27)
            self.lbl_sens.size = (cw, ch * 0.07)
            self.lbl_sens.pos = (x0, y0 + ch * 0.20)
            self.slider.size = (cw * 0.62, ch * 0.08)
            self.slider.pos = (x0 + cw * 0.19, y0 + ch * 0.12)
            bw2 = (cw * 0.94 - 3 * gap) / 4.0
            for k, b in enumerate((self.btn_mundos, self.btn_rede, self.btn_cfg, self.btn_sair)):
                b.size = (bw2, ch * 0.09)
                b.pos = (x0 + cw * 0.03 + k * (bw2 + gap), y0 + ch * 0.015)

    def on_touch_down(self, touch):
        super().on_touch_down(touch)
        return True

    def on_touch_move(self, touch):
        super().on_touch_move(touch)
        return True

    def on_touch_up(self, touch):
        super().on_touch_up(touch)
        return True


class JogoApp(App):
    def liberar_rotacao(self, *args):
        """Android: gira com o celular (paisagem/retrato) mesmo com a rotação automática desligada."""
        try:
            from jnius import autoclass
            ato = None
            for nome in ('org.kivy.android.PythonActivity', 'org.renpy.android.PythonActivity'):
                try:
                    ato = autoclass(nome).mActivity
                    if ato is not None:
                        break
                except Exception:
                    ato = None
            if ato is None:
                return
            try:
                from android.runnable import run_on_ui_thread
                run_on_ui_thread(lambda: ato.setRequestedOrientation(10))()   # FULL_SENSOR
            except Exception:
                ato.setRequestedOrientation(10)
        except Exception:
            pass   # fora do Android (ou sem jnius): sem problema

    def build(self):
        self.liberar_rotacao()
        Window.clearcolor = (0.05, 0.05, 0.06, 1)
        self.raiz = FloatLayout()
        self.cena = Cena()
        for k, v in CONFIG.get('opcoes', {}).items():
            if k in [o[1] for o in Menu.OPCOES] and hasattr(self.cena, k):
                setattr(self.cena, k, v)
        self.raiz.add_widget(self.cena)
        self.hud = Label(text='', size_hint=(None, None), halign='left', valign='middle', font_size='17sp',
                         outline_width=2, outline_color=(0, 0, 0))
        self.hud.bind(size=lambda inst, s: setattr(inst, 'text_size', s))
        self.raiz.add_widget(self.hud)
        self.btn_pulo = Botao(icone='seta', forma='circulo', ao_tocar=self.cena.pular, imediato=True, repetir=0.12)
        self.btn_menu = Botao(icone='menu', forma='circulo', ao_tocar=lambda: self.abrir_menu('pausa'))
        self.btn_cam = Botao(icone='camera', forma='circulo', ao_tocar=self.trocar_camera)
        self.btn_mochila = Botao(icone='mochila', forma='circulo', ao_tocar=lambda: self.abrir_menu('inventario'))
        self.raiz.add_widget(self.btn_mochila)
        self.raiz.add_widget(self.btn_cam)
        self.btn_desce = Botao(icone='seta_baixo', forma='circulo', ao_tocar=lambda: self.cena.subir(-1.0), imediato=True, repetir=0.12)
        self.btn_plantar = Botao(texto='+ Árvore', fonte='15sp', ao_tocar=self.cena.plantar)
        self.btn_cortar = Botao(texto='Machado', fonte='15sp', ao_tocar=self.cena.cortar)
        self.btn_correr = Botao(texto='Correr', fonte='15sp', ao_tocar=self.alternar_correr)
        self.raiz.add_widget(self.btn_correr)
        for wd in (self.btn_desce, self.btn_plantar, self.btn_cortar):
            self.raiz.add_widget(wd)
        self.raiz.add_widget(self.btn_pulo)
        self.raiz.add_widget(self.btn_menu)
        self.menu = Menu(self)
        self.painel_erro = None
        self.cena.hud = self.hud
        self.cena.ao_vencer = self.mostrar_vitoria
        self.cena.ao_erro = self.mostrar_erro
        self.botoes_mundo(False)
        Clock.schedule_interval(self.menu.tick, 0.5)
        Window.softinput_mode = 'below_target'
        self.raiz.bind(size=self.organizar)
        self.organizar()
        self.abrir_menu('perfil' if PERFIL is None else 'inicio')
        return self.raiz

    def organizar(self, *args):
        W, H = self.raiz.size
        if W < 10 or H < 10:
            W, H = Window.size
        s = H * 0.26
        self.btn_pulo.size = (s, s)
        self.btn_pulo.pos = (W - s - H * 0.05, H * 0.07)
        m = H * 0.12
        self.btn_menu.size = (m, m)
        self.btn_menu.pos = (W - m - H * 0.03, H - m - H * 0.03)
        self.btn_cam.size = (m, m)
        self.btn_cam.pos = (W - 2 * m - H * 0.06, H - m - H * 0.03)
        d = H * 0.17
        self.btn_desce.size = (d, d)
        self.btn_desce.pos = (W - s - H * 0.05 - d - H * 0.03, H * 0.07)
        self.btn_plantar.size = self.btn_cortar.size = (H * 0.32, H * 0.10)
        self.btn_plantar.pos = (W - H * 0.32 - H * 0.03, H * 0.60)
        self.btn_cortar.pos = (W - H * 0.32 - H * 0.03, H * 0.48)
        self.btn_correr.size = (H * 0.24, H * 0.10)
        self.btn_correr.pos = (H * 0.04, H * 0.54)
        self.btn_mochila.size = (m, m)
        self.btn_mochila.pos = (W - 3 * m - H * 0.09, H - m - H * 0.03)
        self.hud.size = (W * 0.62, H * 0.08)
        self.hud.pos = (H * 0.03, H - H * 0.11)
        self.menu.size = (W, H)
        self.menu.pos = (0, 0)

    def abrir_menu(self, modo='inicio', titulo=None, edicao=False):
        self.cena.pausado = True
        self.cena.soltar_controles()
        self.btn_menu.opacity = 0.0
        self.btn_cam.opacity = 0.0
        self.btn_mochila.opacity = 0.0
        self.btn_mochila.disabled = True
        self.btn_pulo.opacity = 0.0
        self.botoes_mundo(False)
        self.menu.preparar(modo, titulo or {'pausa': 'PAUSA', 'config': 'CONFIGURAÇÕES', 'rede': 'MULTIJOGADOR',
                                            'mundos': 'MEUS MUNDOS', 'inventario': 'MOCHILA', 'novo': 'NOVO MUNDO',
                                            'cheats': 'CHEATS', 'perfil': 'SEU PERSONAGEM' if edicao else 'CRIE SEU PERSONAGEM'}.get(modo, Menu.NOME_JOGO), edicao)
        if self.menu.parent is None:
            self.raiz.add_widget(self.menu)

    def fechar_menu(self, *args):
        self.cena.pausado = False
        self.btn_menu.opacity = 1.0
        self.btn_cam.opacity = 1.0
        self.btn_mochila.opacity = 1.0
        self.btn_mochila.disabled = False
        self.btn_pulo.opacity = 1.0
        self.botoes_mundo(True)
        if self.menu.parent is not None:
            self.raiz.remove_widget(self.menu)

    def alternar_correr(self):
        self.cena.correr = not self.cena.correr
        self.btn_correr.ativo = self.cena.correr
        self.btn_correr.redesenhar()

    def botoes_mundo(self, jogando):
        c = self.cena
        self.btn_correr.opacity = 1.0 if jogando else 0.0
        self.btn_correr.disabled = not jogando
        for wd, ver in ((self.btn_plantar, bool(c.cheats.get('plantar'))), (self.btn_cortar, bool(c.cheats.get('machado'))),
                        (self.btn_desce, bool(c.cheats.get('voar')))):
            sim = jogando and ver
            wd.opacity = 1.0 if sim else 0.0
            wd.disabled = not sim

    def escolher_mundo(self, cfg):
        self.cena.carregar_mundo(cfg)
        self.fechar_menu()

    def trocar_camera(self, *args):
        ordem = ['primeira', 'terceira', 'segunda']
        self.cena.camera = ordem[(ordem.index(self.cena.camera) + 1) % 3]

    def sair_para_menu(self, *args):
        self.cena.soltar_controles()
        self.abrir_menu('inicio')

    def escolher(self, chave):
        self.cena.carregar(chave)
        self.fechar_menu()

    def mostrar_vitoria(self, tempo):
        self.abrir_menu('inicio', f"Você venceu em {tempo:.1f}s!")

    def mostrar_erro(self, texto):
        linhas = texto.strip().splitlines()[-16:]
        msg = "Ocorreu um erro. Tire um print desta tela e me envie.\n\n" + "\n".join(linhas)
        if self.painel_erro is None:
            self.painel_erro = Label(text=msg, font_size='11sp', halign='left', valign='top',
                                     color=(1, 1, 1, 1), size_hint=(0.96, 0.92),
                                     pos_hint={'center_x': 0.5, 'center_y': 0.5})
            self.painel_erro.bind(size=lambda inst, s: setattr(inst, 'text_size', (s[0] - 20, s[1] - 20)))
            with self.painel_erro.canvas.before:
                Color(0.04, 0.05, 0.07, 0.96)
                self._fundo_erro = Rectangle(pos=(0, 0), size=(10, 10))
            self.painel_erro.bind(pos=lambda i, p: setattr(self._fundo_erro, 'pos', p),
                                  size=lambda i, s: setattr(self._fundo_erro, 'size', s))
        else:
            self.painel_erro.text = msg
        if self.painel_erro.parent is None:
            self.raiz.add_widget(self.painel_erro)


if __name__ == '__main__':
    JogoApp().run()
