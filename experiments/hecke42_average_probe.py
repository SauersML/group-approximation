#!/usr/bin/env python3
"""Probe the single-Hecke-average isometry wall on approximate SL3(Z[1/2]) models.

Target claim: single-hecke-average-isometry-for-lambda-central-unitaries.
For every regular-trace matrix model of Gamma = SL_3(Z[1/2]) and every
almost-SL_3(Z)-central unitary k, the lazy average

    S(k) = (1/2) k + (1/(2L)) sum_i rho(w_i) k rho(w_i)^*,

over the L = 42 left-coset words w_i = u_i h of Lambda h Lambda
(h = diag(2,1,1/2); expanding-double-coset-degree-is-p-times-flags),
should satisfy ||S(k)||_2 = 1.  The exact quasi-regular enemy sits at
||S(k)||_2^2 = 43/168.  Exact congruence models provably sit at 1
(co-density + property (T)), so this probe searches the APPROXIMATE
representation variety directly: variables are unitaries for the six
elementary generators of SL_3(Z), one unitary V ~ rho(h), and the
witness k; penalties are Steinberg-relation defects, the six
h-conjugation (expansion) relations, a regular-trace penalty on short
nontrivial words (nontriviality certified in the faithful rational
matrix image), and the Lambda-centrality of k.  Reported: Pareto
points (||S(k)||_2^2, E_C, D_rel, R_reg) over restarts and sizes.

Reading the output: floors of ||S(k)||_2^2 near 1 while penalties
vanish support the isometry claim; drift toward 43/168 with all
penalties -> 0 would be enemy evidence and must be handed to the
graph, not silently believed (see the node's falsification gate).

Scope honesty: minimization is nonconvex; a high floor here is
evidence, never proof.  This is the finite-level shadow probe the
exact-quotient PRT1 probe cannot perform (h has no image mod 2^k).

Selftest (integer-only, no linear algebra):
    python3 hecke42_average_probe.py --selftest
verifies L = 42 by BFS coset enumeration in SL_3(Z/4) and checks the
42 representative words against the parahoric membership test.

Run (MSI lane only; do not run the optimization locally):
    python3 hecke42_average_probe.py --d 16 --restarts 8
Output: JSON lines per restart and hecke42-average-probe.json.
"""
from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction

import numpy as np

rng = np.random.default_rng(20260842)

# ---------------------------------------------------------------------------
# Integer layer: generators, BFS over SL3(Z/4), the 42 coset words.
# ---------------------------------------------------------------------------

# Elementary generators of SL_3(Z): name -> (i, j) for e_ij(1).
ELEM = {"A": (0, 1), "B": (1, 2), "C": (0, 2),
        "Ap": (1, 0), "Bp": (2, 1), "Cp": (2, 0)}


def elem_mat(i: int, j: int, a) -> list:
    m = [[Fraction(int(r == c)) for c in range(3)] for r in range(3)]
    m[i][j] = Fraction(a)
    return m


def mat_mul(x, y):
    return [[sum(x[r][t] * y[t][c] for t in range(3)) for c in range(3)]
            for r in range(3)]


def mat_mod(x, m):
    return tuple(tuple(int(x[r][c]) % m for c in range(3)) for r in range(3))


def is_identity(x) -> bool:
    return all(x[r][c] == (1 if r == c else 0)
               for r in range(3) for c in range(3))


def in_parahoric_mod4(t) -> bool:
    # S = {A in SL_3(Z/4): 2 | a21, 4 | a31, 2 | a32}
    return t[1][0] % 2 == 0 and t[2][0] % 4 == 0 and t[2][1] % 2 == 0


def coset_words_mod4():
    """BFS over SL_3(Z/4) with elementary generators; return 42 words
    (as lists of (name, exp) with exp in {1,-1}) whose cosets u S are
    pairwise distinct and exhaust SL_3(Z/4)/S."""
    gens = []
    for name, (i, j) in ELEM.items():
        gens.append((name, 1, mat_mod(elem_mat(i, j, 1), 4)))
        gens.append((name, -1, mat_mod(elem_mat(i, j, -1), 4)))

    def mul4(t, u):
        return tuple(tuple(sum(t[r][k] * u[k][c] for k in range(3)) % 4
                           for c in range(3)) for r in range(3))

    ident = mat_mod(elem_mat(0, 1, 0), 4)
    seen = {ident}
    frontier = [(ident, [])]
    reps = []  # (matrix mod 4, word)
    all_elems = {ident: []}
    while frontier:
        nxt = []
        for t, w in frontier:
            for name, e, g in gens:
                u = mul4(t, g)
                if u not in seen:
                    seen.add(u)
                    all_elems[u] = w + [(name, e)]
                    nxt.append((u, w + [(name, e)]))
        frontier = nxt
    assert len(all_elems) == 43008, len(all_elems)

    def coset_key(t):
        # canonical key of t*S: orbit of t under right mult by S is
        # expensive; instead key by the S-invariant data of columns.
        # Use: reduce via membership test against chosen reps.
        return None

    for t, w in sorted(all_elems.items(), key=lambda kv: (len(kv[1]), kv[0])):
        new = True
        for r, _ in reps:
            # same coset iff r^{-1} t in S; invert r mod 4 via adjugate.
            ri = inv_mod4(r)
            if in_parahoric_mod4(mul4(ri, t)):
                new = False
                break
        if new:
            reps.append((t, w))
    assert len(reps) == 42, len(reps)
    return [w for _, w in reps]


def inv_mod4(t):
    # adjugate / det for 3x3 over Z/4 (det = 1 in SL_3).
    def cof(r, c):
        rs = [x for x in range(3) if x != r]
        cs = [x for x in range(3) if x != c]
        return (t[rs[0]][cs[0]] * t[rs[1]][cs[1]]
                - t[rs[0]][cs[1]] * t[rs[1]][cs[0]])
    adj = tuple(tuple(((-1) ** (r + c) * cof(c, r)) % 4 for c in range(3))
                for r in range(3))
    return adj


def word_to_matrix(word) -> list:
    m = elem_mat(0, 1, 0)
    for name, e in word:
        i, j = ELEM[name]
        m = mat_mul(m, elem_mat(i, j, e))
    return m


def short_nontrivial_words(max_len: int):
    """Words over the 7 generators (elementaries + h) of length <=
    max_len that are nontrivial in SL_3(Z[1/2]) (checked in the
    faithful rational image).  Deduplicated by the rational matrix."""
    H = [[Fraction(2), 0, 0], [0, Fraction(1), 0], [0, 0, Fraction(1, 2)]]
    Hi = [[Fraction(1, 2), 0, 0], [0, Fraction(1), 0], [0, 0, Fraction(2)]]
    gens = []
    for name, (i, j) in ELEM.items():
        gens.append(((name, 1), elem_mat(i, j, 1)))
        gens.append(((name, -1), elem_mat(i, j, -1)))
    gens.append((("V", 1), H))
    gens.append((("V", -1), Hi))
    out, seen = [], set()
    frontier = [([], elem_mat(0, 1, 0))]
    for _ in range(max_len):
        nxt = []
        for w, m in frontier:
            for sym, g in gens:
                w2, m2 = w + [sym], mat_mul(m, g)
                key = tuple(tuple(m2[r][c] for c in range(3)) for r in range(3))
                nxt.append((w2, m2))
                if key in seen or is_identity(m2):
                    continue
                seen.add(key)
                out.append(w2)
        frontier = nxt
    return out


# ---------------------------------------------------------------------------
# Unitary layer: words, traces, gradients.
# ---------------------------------------------------------------------------

def word_product(word, env):
    d = next(iter(env.values())).shape[0]
    m = np.eye(d, dtype=complex)
    for name, e in word:
        X = env[name]
        m = m @ (X if e == 1 else X.conj().T)
    return m


def grad_re_tr(word, env, coeff):
    """Accumulate d/dX of Re(coeff * tr(prod word)) into a dict of
    Euclidean gradients, via prefix/suffix products."""
    d = next(iter(env.values())).shape[0]
    mats = [env[n] if e == 1 else env[n].conj().T for n, e in word]
    k = len(mats)
    pre = [np.eye(d, dtype=complex)]
    for m in mats[:-1]:
        pre.append(pre[-1] @ m)
    suf = [np.eye(d, dtype=complex)]
    for m in reversed(mats[1:]):
        suf.append(m @ suf[-1])
    suf = suf[::-1]
    grads = {}
    for t, (name, e) in enumerate(word):
        RL = suf[t] @ pre[t]
        if e == 1:
            g = np.conj(coeff) * RL.conj().T
        else:
            g = coeff * RL
        grads[name] = grads.get(name, 0) + g
    return grads


class Objective:
    """F = ||S(k)||_2^2 + beta*E_C + gamma*D_rel + zeta*R_reg,
    every term expressed through Re tr(word)/d and |tr(word)/d|^2."""

    def __init__(self, coset_words, rel_words, reg_words, lam_gens,
                 beta, gamma, zeta):
        self.cw = coset_words
        self.rel = rel_words      # list of words whose product should be I
        self.reg = reg_words      # nontrivial words, want tr ~ 0
        self.lam = lam_gens       # names of Lambda generators
        self.beta, self.gamma, self.zeta = beta, gamma, zeta

    @staticmethod
    def conj_word(w, inner):
        # w * inner * w^{-1}
        winv = [(n, -e) for n, e in reversed(w)]
        return list(w) + list(inner) + winv

    def s_norm_sq(self, env):
        # ||S(k)||^2 = (1/4)+(1/(4L^2)) sum_ij Re tr(k_i k_j^*)/d cross
        # terms with k; expand: S(k) = a0 k + a1 sum conj_i(k),
        # ||S(k)||^2 = sum_{terms} a_x a_y <term_x, term_y>.
        d = env["k"].shape[0]
        L = len(self.cw)
        terms = [[("k", 1)]]
        for w in self.cw:
            wV = list(w) + [("V", 1)]
            terms.append(self.conj_word(wV, [("k", 1)]))
        coefs = [0.5] + [1.0 / (2 * L)] * L
        val = 0.0
        for x in range(len(terms)):
            for y in range(len(terms)):
                inner = terms[x] + [(n, -e) for n, e in reversed(terms[y])]
                val += coefs[x] * coefs[y] * \
                    np.trace(word_product(inner, env)).real / d
        return val

    def value_and_grad(self, env):
        d = env["k"].shape[0]
        L = len(self.cw)
        grads = {n: np.zeros((d, d), dtype=complex) for n in env}
        val = 0.0

        def add(gd):
            for n, g in gd.items():
                grads[n] += g

        # ||S(k)||^2 (quadratic in many words; assemble pairwise)
        terms = [[("k", 1)]]
        for w in self.cw:
            wV = list(w) + [("V", 1)]
            terms.append(self.conj_word(wV, [("k", 1)]))
        coefs = [0.5] + [1.0 / (2 * L)] * L
        for x in range(len(terms)):
            for y in range(len(terms)):
                inner = terms[x] + [(n, -e) for n, e in reversed(terms[y])]
                c = coefs[x] * coefs[y] / d
                val += c * np.trace(word_product(inner, env)).real * 1.0
                add(grad_re_tr(inner, env, c))

        # E_C: sum over Lambda generators of 2 - 2 Re tr(k c k* c*)/d
        for n in self.lam:
            w = [("k", 1), (n, 1), ("k", -1), (n, -1)]
            t = np.trace(word_product(w, env)).real / d
            val += self.beta * (2 - 2 * t)
            add(grad_re_tr(w, env, -2 * self.beta / d))

        # D_rel: each relation word should be I: 2 - 2 Re tr(w)/d
        for w in self.rel:
            t = np.trace(word_product(w, env)).real / d
            val += self.gamma * (2 - 2 * t)
            add(grad_re_tr(w, env, -2 * self.gamma / d))

        # R_reg: |tr(w)/d|^2 for nontrivial words
        for w in self.reg:
            t = np.trace(word_product(w, env)) / d
            val += self.zeta * abs(t) ** 2
            add(grad_re_tr(w, env, 2 * self.zeta * np.conj(t) / d))

        return val, grads


def relation_words():
    """Relation words (product == identity) for the probe: Steinberg
    unipotent relations and the six h-expansion relations.  NOT a
    complete presentation; recorded as such."""
    rels = []

    def comm(a, b):
        return [a, b, (a[0], -a[1]), (b[0], -b[1])]

    # [A,B] = C ; [A,C]=[B,C]=1 ; [Bp,Ap] = Cp ; [Ap,Cp]=[Bp,Cp]=1
    rels.append(comm(("A", 1), ("B", 1)) + [("C", -1)])
    rels.append(comm(("A", 1), ("C", 1)))
    rels.append(comm(("B", 1), ("C", 1)))
    rels.append(comm(("Bp", 1), ("Ap", 1)) + [("Cp", -1)])
    rels.append(comm(("Ap", 1), ("Cp", 1)))
    rels.append(comm(("Bp", 1), ("Cp", 1)))
    # h-expansions: V A V^-1 A^-2 = 1 etc.; V^-1 Ap V Ap^-2 = 1 etc.
    for n, m in (("A", 2), ("B", 2), ("C", 4)):
        rels.append([("V", 1), (n, 1), ("V", -1)] + [(n, -1)] * m)
    for n, m in (("Ap", 2), ("Bp", 2), ("Cp", 4)):
        rels.append([("V", -1), (n, 1), ("V", 1)] + [(n, -1)] * m)
    return rels


def probe(d, restarts, iters, beta, gamma, zeta, reg_len):
    cw = coset_words_mod4()
    obj = Objective(cw, relation_words(),
                    short_nontrivial_words(reg_len),
                    ["A", "B", "C", "Ap", "Bp", "Cp"],
                    beta, gamma, zeta)
    names = ["A", "B", "C", "Ap", "Bp", "Cp", "V", "k"]
    results = []
    for r in range(restarts):
        env = {}
        for n in names:
            Z = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
            env[n] = np.linalg.qr(Z)[0]
        step = 0.1
        last = None
        for _ in range(iters):
            val, grads = obj.value_and_grad(env)
            if last is not None and abs(last - val) < 1e-10:
                break
            new_env = {}
            for n in names:
                G, X = grads[n], env[n]
                Om = (G @ X.conj().T - X @ G.conj().T) / 2
                nrm = np.linalg.norm(Om)
                if nrm < 1e-14:
                    new_env[n] = X
                    continue
                new_env[n] = np.linalg.qr(
                    (np.eye(d) - step * Om / nrm) @ X)[0]
            nval, _ = obj.value_and_grad(new_env)
            if nval < val:
                env, last, step = new_env, val, min(step * 1.05, 0.3)
            else:
                step *= 0.5
                if step < 1e-7:
                    break
        s2 = obj.s_norm_sq(env)
        _, _ = obj.value_and_grad(env)
        ec = sum(2 - 2 * np.trace(word_product(
            [("k", 1), (n, 1), ("k", -1), (n, -1)], env)).real / d
            for n in obj.lam)
        dr = sum(2 - 2 * np.trace(word_product(w, env)).real / d
                 for w in obj.rel)
        rg = sum(abs(np.trace(word_product(w, env)) / d) ** 2
                 for w in obj.reg)
        rec = {"d": d, "restart": r,
               "S_norm_sq": round(float(s2), 5),
               "E_C": round(float(ec), 5),
               "D_rel": round(float(dr), 5),
               "R_reg": round(float(rg), 5),
               "target_enemy": round(43 / 168, 5)}
        print(json.dumps(rec), flush=True)
        results.append(rec)
    return results


def selftest():
    cw = coset_words_mod4()
    print(f"coset count: {len(cw)} (expected 42)")
    # verify pairwise-distinct cosets once more via the integer layer
    mats = [mat_mod(word_to_matrix(w), 4) for w in cw]
    for i in range(len(mats)):
        for j in range(i + 1, len(mats)):
            def mul4(t, u):
                return tuple(tuple(
                    sum(t[r][k] * u[k][c] for k in range(3)) % 4
                    for c in range(3)) for r in range(3))
            assert not in_parahoric_mod4(mul4(inv_mod4(mats[i]), mats[j]))
    print("42 pairwise-distinct parahoric cosets verified")
    print("SELFTEST-PASS", file=sys.stderr)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--d", type=int, default=16)
    ap.add_argument("--restarts", type=int, default=8)
    ap.add_argument("--iters", type=int, default=300)
    ap.add_argument("--beta", type=float, default=4.0)
    ap.add_argument("--gamma", type=float, default=4.0)
    ap.add_argument("--zeta", type=float, default=1.0)
    ap.add_argument("--reg-len", type=int, default=2)
    args = ap.parse_args()
    if args.selftest:
        selftest()
        return
    res = probe(args.d, args.restarts, args.iters,
                args.beta, args.gamma, args.zeta, args.reg_len)
    with open("hecke42-average-probe.json", "w") as f:
        json.dump(res, f, indent=1)
    print("PROBE-DONE", file=sys.stderr)


if __name__ == "__main__":
    main()
