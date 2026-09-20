#!/usr/bin/env python3
"""Calibration: fibre sums of a nonnegative positive definite function need not be maximal
at the identity or positive definite when the subgroup is nonamenable.

Group: Gamma = F_2 x Z/2, with N = F_2 x 0 and Q = Z/2. Put
    tau(n,0) = delta_e(n),   tau(n,1) = c 1_S(n),   c = 0.27,
where S is the free generating set together with its inverses (|S| = 4).

Positive definiteness on Gamma reduces, through the characters of Z/2, to
positive definiteness of delta_e +- c 1_S on F_2. That holds iff
c ||lambda(1_S)|| <= 1, and Kesten gives ||lambda(1_S)|| = 2 sqrt(3).

The script checks this exactly, then checks positive semidefiniteness of the
Gram matrix of tau on a ball of F_2 x Z/2 numerically. It then computes the
fibre sums sigma(0) = 1 and sigma(1) = 4c = 1.08 > sigma(0). So sigma is not
maximal at e and not positive definite on Q = Z/2.
"""
import math
import numpy as np

c = 0.27
kesten = 2 * math.sqrt(3)
print(f"c*||lambda(1_S)|| = {c*kesten:.4f} (< 1 required)")

# words in F_2 over the letters a, A, b, B, where A = a^-1 and B = b^-1
INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def mul(u, v):
    u = list(u)
    for s in v:
        if u and u[-1] == INV[s]:
            u.pop()
        else:
            u.append(s)
    return ''.join(u)


def inv(u):
    return ''.join(INV[s] for s in reversed(u))


def ball(R):
    B, layer = [''], ['']
    for _ in range(R):
        nl = []
        for w in layer:
            for s in 'aAbB':
                if w and w[-1] == INV[s]:
                    continue
                nl.append(w + s)
        B += nl
        layer = nl
    return B


def tau(g):  # g = (word, bit)
    w, t = g
    if t == 0:
        return 1.0 if w == '' else 0.0
    return c if len(w) == 1 else 0.0


B = [(w, t) for w in ball(4) for t in (0, 1)]
M = np.array([[tau((mul(inv(x[0]), y[0]), (x[1] + y[1]) % 2)) for y in B] for x in B])
ev = np.linalg.eigvalsh(M)
print(f"ball R=4 in F_2 x Z/2: {len(B)} points, min eigenvalue of [tau(x^-1 y)] = {ev.min():.4f}")
sigma0, sigma1 = 1.0, 4 * c
print(f"sigma(0) = {sigma0}, sigma(1) = {sigma1:.2f}; 2x2 matrix [[s0,s1],[s1,s0]] "
      f"has min eigenvalue {sigma0 - sigma1:.2f} < 0")
