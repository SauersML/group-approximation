#!/usr/bin/env python3
"""Float check of the M -> infinity limit: for a log-scale histogram (h, k) on n cells build
    nu_M(m) ~ h_{c(m)} / m,  eta_M(m) ~ k_{c(m)} / m   (m = 1..M, c(m) = cell of log m / log M)
and print Phi(nu_M, eta_M) = BC(nu,eta)^2 + BC(nu*eta, nu) for growing M (float FFT, scouting only).
Usage: finite_m_check.py hist.json e1,e2,...   (M = 2^e)
"""
import sys, json, math
import numpy as np

d = json.load(open(sys.argv[1]))
h = np.array(d['h']); k = np.array(d['k']); n = len(h)
for e in map(int, sys.argv[2].split(',')):
    M = 1 << e
    m = np.arange(1, M + 1, dtype=np.float64)
    c = np.minimum((np.log(m) / math.log(M) * n).astype(np.int64), n - 1)
    nu = h[c] / m; nu /= nu.sum()
    eta = k[c] / m; eta /= eta.sum()
    L = 1 << (2 * M).bit_length()
    conv = np.fft.irfft(np.fft.rfft(nu, L) * np.fft.rfft(eta, L), L)[:M - 1].clip(min=0)  # sizes 2..M
    bc1 = np.sqrt(nu * eta).sum()
    bc2 = np.sqrt(nu[1:] * conv).sum()
    print(json.dumps({'e': e, 'Phi': bc1 ** 2 + bc2, 'normP': (bc1 ** 2 + bc2) / 2, 'bc1sq': bc1 ** 2, 'bc2': bc2}),
          flush=True)
