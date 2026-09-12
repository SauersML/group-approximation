#!/usr/bin/env python3
"""Finite checks for affine tensor linearization; not a proof of the premise.

Run with Python 3 and numpy. Rational checks use fractions.Fraction only.
The proof is in research/artifacts/alpha-plane-affine-tensor-linearization-2026-09-04.md.
"""
from fractions import Fraction as Q
from itertools import product
import json
import math
import numpy as np


def mul(a, b, q, poly):
    ans = 0
    while b:
        if b & 1:
            ans ^= a
        b >>= 1
        a <<= 1
        if a & q:
            a ^= poly
    return ans


def transpose(a):
    return [list(x) for x in zip(*a)]


def mm(a, b):
    return [[sum(x*y for x, y in zip(row, col))
             for col in zip(*b)] for row in a]


def kron(a, b):
    return [[x*y for x in row_a for y in row_b]
            for row_a in a for row_b in b]


def edge_word(r, x, b, t, q, poly):
    a = mul(t, b, q, poly)
    left = mm(r[x ^ b], transpose(r[x]))
    right = mm(r[x ^ a ^ b], transpose(r[x ^ a]))
    return mm(left, transpose(right))


def corr(w):
    return sum(w[i][i] for i in range(len(w))) / len(w)


def exact_check():
    q, poly = 4, 7
    r = [
        [[Q(1), Q(0)], [Q(0), Q(1)]],
        [[Q(1), Q(0)], [Q(0), Q(-1)]],
        [[Q(3,5), Q(-4,5)], [Q(4,5), Q(3,5)]],
        [[Q(5,13), Q(12,13)], [Q(12,13), Q(-5,13)]],
    ]
    eye = [[Q(1), Q(0)], [Q(0), Q(1)]]
    assert all(mm(a, transpose(a)) == eye for a in r)
    assert mm(r[1], r[2]) != mm(r[2], r[1])
    energies = [sum(2-2*corr(edge_word(r,x,b,t,q,poly))
                    for x,b in product(range(q), repeat=2))/q**2
                for t in range(q)]
    f = sum(energies)/q
    assert all(0 <= e <= 2*f for e in energies)
    beta = Q(q-1,q)
    affines = [[mul(u,x,q,poly)^v for x in range(q)]
               for u in range(1,q) for v in range(q)]
    checks = 0
    # Explicit tensor matrices, not the trace-product shortcut, verify (7).
    for x,b in [(0,1),(1,3)]:
        for t in range(q):
            total = Q(0)
            for g,h in product(affines, repeat=2):
                table = [kron(r[g[y]], r[h[y]]) for y in range(q)]
                total += 2-2*corr(edge_word(table,x,b,t,q,poly))
                checks += 1
            observed = total / len(affines)**2
            expected = 2*(1-(1-energies[t]/(2*beta))**2)
            assert observed == expected
    return {"explicit_rational_tensor_word_checks": checks,
            "slope_energies": [str(e) for e in energies], "F": str(f)}


def numeric_energies(r, q, poly):
    d = r.shape[-1]
    slopes = np.zeros(q)
    full = 0.0
    for b in range(q):
        edges = np.array([r[x^b] @ r[x].conj().T for x in range(q)])
        mean = edges.mean(axis=0)
        full += 2*np.mean(np.sum(np.abs(edges-mean)**2,axis=(1,2))/d)/q
        for t in range(q):
            a = mul(t,b,q,poly)
            diff = edges - edges[np.arange(q)^a]
            slopes[t] += np.mean(np.sum(np.abs(diff)**2,axis=(1,2))/d)/q
    return slopes, full


def numerical_check():
    rng = np.random.default_rng(20260904)
    count = 0
    maximum_identity_error = 0.0
    minimum_amplified_F = 2.0
    for q,poly in [(4,7),(8,11),(16,19)]:
        beta = 1-1/q
        for d in [1,2,3,5]:
            for scale in [0.02,0.2,1.0]:
                r = []
                for x in range(q):
                    z = rng.normal(size=(d,d))+1j*rng.normal(size=(d,d))
                    h = (z+z.conj().T)/2
                    vals,vecs = np.linalg.eigh(h)
                    r.append((vecs*np.exp(1j*scale*vals)) @ vecs.conj().T)
                r = np.array(r)
                e,f = numeric_energies(r,q,poly)
                assert abs(e.mean()-f) < 1e-10
                assert np.max(e) <= 2*f+1e-10
                # Independently check complex-conjugate doubling.
                realified = np.array([np.block([[v,np.zeros_like(v)],
                                     [np.zeros_like(v),v.conj()]]) for v in r])
                er,fr = numeric_energies(realified,q,poly)
                assert np.max(np.abs(er-e)) < 1e-10
                for t in range(q):
                    x,b = 1,2
                    a = mul(t,b,q,poly)
                    c = 0j
                    for u in range(1,q):
                        for v in range(q):
                            y = mul(u,x,q,poly)^v
                            bb = mul(u,b,q,poly)
                            aa = mul(u,a,q,poly)
                            w = realified[y^bb] @ realified[y].conj().T
                            w = w @ realified[y^aa] @ realified[y^aa^bb].conj().T
                            c += np.trace(w)/(2*d*q*(q-1))
                    error = abs(c-(1-e[t]/(2*beta)))
                    maximum_identity_error = max(maximum_identity_error,float(error))
                    assert error < 1e-10
                m = 2*q
                diluted_f = f/m
                k = math.ceil(beta/diluted_f)
                z = e/(m*2*beta)
                amplified = 2*beta*(-np.expm1(k*np.log1p(-z)))
                amplified_f = amplified.mean()
                delta = e[1]+e[2]
                assert amplified[1]+amplified[2] <= delta/f+1e-9
                assert amplified_f >= beta*(1-math.exp(-1))-1e-9
                minimum_amplified_F = min(minimum_amplified_F,float(amplified_f))
                count += 1
    return {"complex_unitary_tables_checked": count,
            "fields": [4,8,16], "dimensions": [1,2,3,5],
            "max_affine_correlation_error": maximum_identity_error,
            "min_amplified_F": minimum_amplified_F}


def additive_action_check():
    rng = np.random.default_rng(140901)
    worst = 0.0
    for q,poly in [(4,7),(8,11),(16,19)]:
        for d in [2,3,5]:
            chars_x = rng.integers(q,size=d)
            chars_z = rng.integers(q,size=d)
            v,_ = np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))
            x = np.array([np.diag([(-1)**int(int(a&c).bit_count())
                          for c in chars_x]) for a in range(q)])
            z = np.array([v @ np.diag([(-1)**int(int(b&c).bit_count())
                          for c in chars_z]) @ v.conj().T for b in range(q)])
            r = x @ z
            for a,b,c in product(range(q),repeat=3):
                edge1 = r[c^b] @ r[c].conj().T
                edge2 = r[c^a^b] @ r[c^a].conj().T
                lhs = np.sum(np.abs(edge1-edge2)**2)/d
                rhs = np.sum(np.abs(x[a]@z[b]-z[b]@x[a])**2)/d
                worst = max(worst,float(abs(lhs-rhs)))
                assert abs(lhs-rhs) < 1e-10
    return {"exact_additive_action_pairs": 9,
            "max_product_table_identity_error": worst}


if __name__ == "__main__":
    print(json.dumps({"exact": exact_check(), "numerical": numerical_check(),
          "additive_actions": additive_action_check(),
          "scope": "Finite checks of algebraic identities and amplification bounds; not a proof of the qualitative premise or nonhyperlinearity."}, indent=2))
