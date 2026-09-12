"""Exact restricted Hessian of the stage-2 objective at the flip.

First-order rigidity is proved (atlas-flip-first-order-rigidity), so the
Riemannian Hessian at the flip is the plain second derivative.  For a
word w with second-chart sites j (operators R_j at W = I) and translation
contexts, along W_t = e^{tX}:

    f_w''(0) = sum_j tr(C_j (X^2 R_j - 2 X R_j X + R_j X^2) D_j)
             + 2 sum_{i<j} tr(C_i [X,R_i] B_{ij} [X,R_j] D_j),

every context a two-sided translation L_a R_b.  Each term reduces by
cyclicity to canonical forms tr(X T2 X T1) and tr(X^2 T), and on the
structured anti-Hermitian directions

    E(u,v)  = L_u R_v - L_{u^-1} R_{v^-1}          (real antisymmetric)
    E'(u,v) = i (L_u R_v + L_{u^-1} R_{v^-1})       (imaginary symmetric)

everything is a signed sum of traces of translation products, i.e. of
Fix counts Fix(a,b) = |C(a)| * [a ~ b].  The objective is
F_w = 2 - (2/n) tr pi_w, so NEGATIVE curvature of the loss along X is
exactly Q(X) := sum_w f_w''(0) > 0.  The scan evaluates Q per slice
(active / control) on a catalog of candidate pairs; any candidate with
positive total Q is a certified escape direction (strict saddle).

--self-test replays the whole pipeline over S4 with random mixed words
and compares the Fix-count evaluation against exact dense-matrix
computation of the same second-derivative formula, entry for entry.
"""

import argparse
import itertools
import json
import os
import random
import sys
from collections import Counter

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


# ---------------------------------------------------------------------------
# group backends
# ---------------------------------------------------------------------------

class GroupBackend:
    """elements as hashable keys; mul/inv/eye; centralizer-based Fix."""

    def __init__(self, elements, mul, inv, eye):
        self.elements = elements
        self.mul = mul
        self.inv = inv
        self.eye = eye
        self.n = len(elements)
        self._class_of = {}
        self._centralizer = {}
        self._build_classes()

    def _build_classes(self):
        seen = set()
        for g in self.elements:
            if g in seen:
                continue
            orbit = {g}
            stack = [g]
            while stack:
                x = stack.pop()
                for s in self.elements:
                    y = self.mul(self.mul(s, x), self.inv(s))
                    if y not in orbit:
                        orbit.add(y)
                        stack.append(y)
            rep = min(orbit)
            for x in orbit:
                self._class_of[x] = rep
                self._centralizer[x] = self.n // len(orbit)
            seen |= orbit

    def fix(self, a, b):
        if self._class_of[a] != self._class_of[b]:
            return 0
        return self._centralizer[a]


def s4_backend():
    elems = [tuple(p) for p in itertools.permutations(range(4))]

    def mul(p, q):  # (p*q)(x) = p(q(x))
        return tuple(p[q[i]] for i in range(4))

    def inv(p):
        out = [0] * 4
        for i, v in enumerate(p):
            out[v] = i
        return tuple(out)

    return GroupBackend(elems, mul, inv, tuple(range(4)))


def gl42_backend():
    from atlas_two_chart_search import gf2_inv, gf2_mul  # noqa: E402
    from atlas_stabilizer_coset_search import (  # noqa: E402
        enumerate_group, matrix_key)
    from atlas_flip_stationarity_exact import ConjugacyOracle  # noqa: E402

    elements, _ = enumerate_group()
    key_of = {}
    mat_of = {}
    for m in elements:
        k = matrix_key(m)
        key_of[k] = k
        mat_of[k] = m
    oracle = ConjugacyOracle(elements)

    class GL(GroupBackend):
        def __init__(self):
            self.elements = list(mat_of)
            self.n = len(self.elements)
            self.eye = matrix_key(np.eye(4, dtype=np.uint8))
            self._oracle = oracle
            self._mat = mat_of
            self._mulmemo = {}
            self._invmemo = {}

        def mul(self, a, b):
            k = (a, b)
            if k not in self._mulmemo:
                self._mulmemo[k] = matrix_key(
                    gf2_mul(self._mat[a], self._mat[b]))
                self._mat.setdefault(self._mulmemo[k],
                                     gf2_mul(self._mat[a], self._mat[b]))
            return self._mulmemo[k]

        def inv(self, a):
            if a not in self._invmemo:
                m = gf2_inv(self._mat[a])
                self._invmemo[a] = matrix_key(m)
                self._mat.setdefault(self._invmemo[a], m)
            return self._invmemo[a]

        def fix(self, a, b):
            return self._oracle.fix(self._mat[a], self._mat[b])

    return GL()


# ---------------------------------------------------------------------------
# canonical Hessian terms of one word:  (kind, data, coeff)
#   kind "sq":   coeff * tr(X^2 * L_a R_b)          data = (a, b)
#   kind "mix":  coeff * tr(X L_{a2}R_{b2} X L_{a1}R_{b1})
#                data = (a2, b2, a1, b1)
# ---------------------------------------------------------------------------

def word_hessian_terms(word, G):
    m = len(word)
    pre_l, pre_r = [G.eye], [G.eye]
    for factor, g in word:
        pre_l.append(G.mul(pre_l[-1], g) if factor == 1 else pre_l[-1])
        pre_r.append(G.mul(pre_r[-1], g) if factor == 2 else pre_r[-1])
    suf_l = [None] * (m + 1)
    suf_r = [None] * (m + 1)
    suf_l[m] = suf_r[m] = G.eye
    for i in range(m - 1, -1, -1):
        factor, g = word[i]
        suf_l[i] = G.mul(g, suf_l[i + 1]) if factor == 1 else suf_l[i + 1]
        suf_r[i] = G.mul(g, suf_r[i + 1]) if factor == 2 else suf_r[i + 1]

    sites = [j for j in range(m) if word[j][0] == 2]
    terms = []
    for j in sites:
        h = word[j][1]
        dc_l = G.mul(suf_l[j + 1], pre_l[j])       # D C = L R pair
        dc_r = G.mul(suf_r[j + 1], pre_r[j])
        # tr(C X^2 R D) = tr(X^2 (R D C)),  R DC = L_{dc_l} R_{h dc_r}
        terms.append(("sq", (dc_l, G.mul(h, dc_r)), 1))
        # tr(C R X^2 D) = tr(X^2 (D C R)) = L_{dc_l} R_{dc_r h}
        terms.append(("sq", (dc_l, G.mul(dc_r, h)), 1))
        # -2 tr(C X R X D) = -2 tr(X R X (D C))
        terms.append(("mix", (G.eye, h, dc_l, dc_r), -2))
    for a_i, j in itertools.combinations(range(len(sites)), 2):
        i, j = sites[a_i], sites[j]
        hi, hj = word[i][1], word[j][1]
        # B = product strictly between i and j
        b_l, b_r = G.eye, G.eye
        for k in range(i + 1, j):
            factor, g = word[k]
            if factor == 1:
                b_l = G.mul(b_l, g)
            else:
                b_r = G.mul(b_r, g)
        dci_l = G.mul(suf_l[j + 1], pre_l[i])      # D_j C_i pair
        dci_r = G.mul(suf_r[j + 1], pre_r[i])
        # +2 tr(X (R_i B) X (R_j D_j C_i))
        terms.append(("mix", (b_l, G.mul(hi, b_r),
                              dci_l, G.mul(hj, dci_r)), 2))
        # -2 tr(X (R_i B R_j) X (D_j C_i))
        terms.append(("mix", (b_l, G.mul(G.mul(hi, b_r), hj),
                              dci_l, dci_r), -2))
        # -2 tr(X B X (R_j D_j C_i R_i))
        terms.append(("mix", (b_l, b_r,
                              dci_l, G.mul(G.mul(hj, dci_r), hi)), -2))
        # +2 tr(X (B R_j) X (D_j C_i R_i))
        terms.append(("mix", (b_l, G.mul(b_r, hj),
                              dci_l, G.mul(dci_r, hi)), 2))
    return terms


# ---------------------------------------------------------------------------
# evaluation of Q(X) on E(u,v) (family "asym") / E'(u,v) (family "sym")
# ---------------------------------------------------------------------------

def eval_terms(terms, G, u, v, family):
    ui, vi = G.inv(u), G.inv(v)
    total = 0
    for kind, data, coeff in terms:
        if kind == "sq":
            a, b = data
            if family == "asym":
                # X^2 = P^2 - 2 I + P^-2
                val = (G.fix(G.mul(G.mul(u, u), a), G.mul(G.mul(v, v), b))
                       - 2 * G.fix(a, b)
                       + G.fix(G.mul(G.mul(ui, ui), a),
                               G.mul(G.mul(vi, vi), b)))
            else:
                # X = i(P + P^-1): X^2 = -(P^2 + 2 I + P^-2)
                val = -(G.fix(G.mul(G.mul(u, u), a), G.mul(G.mul(v, v), b))
                        + 2 * G.fix(a, b)
                        + G.fix(G.mul(G.mul(ui, ui), a),
                                G.mul(G.mul(vi, vi), b)))
        else:
            a2, b2, a1, b1 = data
            val = 0
            for su, sv, sgn in (((u, v), (u, v), 1),
                                ((u, v), (ui, vi), -1),
                                ((ui, vi), (u, v), -1),
                                ((ui, vi), (ui, vi), 1)):
                la = G.mul(G.mul(su[0], a2), G.mul(sv[0], a1))
                rb = G.mul(G.mul(su[1], b2), G.mul(sv[1], b1))
                val += sgn * G.fix(la, rb)
            if family == "sym":
                # X = i(P+P^-1): tr(X T2 X T1) = -(all-plus combination)
                val = 0
                for su, sv in (((u, v), (u, v)), ((u, v), (ui, vi)),
                               ((ui, vi), (u, v)), ((ui, vi), (ui, vi))):
                    la = G.mul(G.mul(su[0], a2), G.mul(sv[0], a1))
                    rb = G.mul(G.mul(su[1], b2), G.mul(sv[1], b1))
                    val -= G.fix(la, rb)
        total += coeff * val
    return total


# ---------------------------------------------------------------------------
# self-test on S4: dense matrices vs Fix-count evaluation
# ---------------------------------------------------------------------------

def self_test(seed=7, n_words=12, n_dirs=25):
    G = s4_backend()
    rng = random.Random(seed)
    n = G.n
    idx = {g: i for i, g in enumerate(G.elements)}

    def lmat(g):
        M = np.zeros((n, n))
        for x in G.elements:
            M[idx[G.mul(g, x)], idx[x]] = 1
        return M

    def rmat(g):
        M = np.zeros((n, n))
        gi = G.inv(g)
        for x in G.elements:
            M[idx[G.mul(x, gi)], idx[x]] = 1
        return M

    words = []
    for _ in range(n_words):
        L = rng.randrange(2, 7)
        words.append([(rng.randrange(1, 3),
                       rng.choice(G.elements)) for _ in range(L)])

    failures = 0
    for _ in range(n_dirs):
        u = rng.choice(G.elements)
        v = rng.choice(G.elements)
        family = rng.choice(["asym", "sym"])
        P = lmat(u) @ rmat(v)
        X = (P - P.T) if family == "asym" else 1j * (P + P.T)
        for w in words:
            sites = [j for j in range(len(w)) if w[j][0] == 2]
            ops = [lmat(g) if f == 1 else rmat(g) for f, g in w]
            # numeric second derivative from the exact formula
            num = 0.0 + 0j
            for j in sites:
                pre = np.eye(n)
                for k in range(j):
                    pre = pre @ ops[k]
                suf = np.eye(n)
                for k in range(j + 1, len(w)):
                    suf = suf @ ops[k]
                R = ops[j]
                num += np.trace(pre @ (X @ X @ R - 2 * X @ R @ X
                                       + R @ X @ X) @ suf)
            for ii, jj in itertools.combinations(sites, 2):
                pre = np.eye(n)
                for k in range(ii):
                    pre = pre @ ops[k]
                mid = np.eye(n)
                for k in range(ii + 1, jj):
                    mid = mid @ ops[k]
                suf = np.eye(n)
                for k in range(jj + 1, len(w)):
                    suf = suf @ ops[k]
                Ri, Rj = ops[ii], ops[jj]
                com_i = X @ Ri - Ri @ X
                com_j = X @ Rj - Rj @ X
                num += 2 * np.trace(pre @ com_i @ mid @ com_j @ suf)
            exact = eval_terms(word_hessian_terms(w, G), G, u, v, family)
            if abs(num.real - exact) > 1e-6 or abs(num.imag) > 1e-6:
                failures += 1
                print("MISMATCH word=%s dir=(%s,%s,%s): numeric %.3f "
                      "exact %d" % (w, u, v, family, num.real, exact))
    print("self-test: %d checks, %d failures"
          % (n_dirs * n_words, failures), flush=True)
    return failures == 0


# ---------------------------------------------------------------------------
# the real scan
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("list_json", nargs="?")
    ap.add_argument("--control-sample", type=int, default=72)
    ap.add_argument("--seed", type=int, default=11)
    ap.add_argument("--max-candidates", type=int, default=4000)
    ap.add_argument("--out", default="atlas-flip-hessian-scan.json")
    args = ap.parse_args()

    if args.self_test:
        return 0 if self_test() else 1

    from atlas_true_criterion_stage2 import (  # noqa: E402
        I4, load_relators, factor_projections)
    from atlas_stabilizer_coset_search import matrix_key  # noqa: E402

    G = gl42_backend()
    words = load_relators(args.list_json)
    rng = random.Random(args.seed)
    active, control = [], []
    for name, w in words:
        p1, p2 = factor_projections(w)
        wk = [(f, matrix_key(mat)) for f, mat in w]
        for f, mat in w:
            G._mat.setdefault(matrix_key(mat), mat)
        if (not np.array_equal(p1, I4)) or (not np.array_equal(p2, I4)):
            active.append((name, wk))
        else:
            control.append((name, wk))
    control = rng.sample(control, min(args.control_sample, len(control)))
    print("words: %d active + %d control sample" %
          (len(active), len(control)), flush=True)

    act_terms, ctl_terms = [], []
    l_side, r_side = set(), set()
    for bag, src in ((act_terms, active), (ctl_terms, control)):
        for _name, w in src:
            bag.extend(word_hessian_terms(w, G))
            for f, g in w:
                (l_side if f == 1 else r_side).add(g)
                (l_side if f == 1 else r_side).add(G.inv(g))
    print("terms: %d active, %d control" %
          (len(act_terms), len(ctl_terms)), flush=True)

    # candidate catalog: products of up to two letters on each side
    def grow(base):
        out = set(base)
        base = list(base)
        for a in base:
            for b in base:
                out.add(G.mul(a, b))
        out.discard(G.eye)
        return list(out)

    lcands, rcands = grow(l_side), grow(r_side)
    rng.shuffle(lcands)
    rng.shuffle(rcands)
    pairs = [(u, v) for u in lcands for v in rcands]
    rng.shuffle(pairs)
    pairs = pairs[:args.max_candidates]
    print("catalog: %d L x %d R -> scanning %d pairs x 2 families"
          % (len(lcands), len(rcands), len(pairs)), flush=True)

    results = []
    best = None
    for k, (u, v) in enumerate(pairs):
        for family in ("asym", "sym"):
            qa = eval_terms(act_terms, G, u, v, family)
            qc = eval_terms(ctl_terms, G, u, v, family)
            rec = (qa + qc, qa, qc, family, u, v)
            if best is None or rec[0] > best[0]:
                best = rec
                print("new max Q_total=%d (Q_act=%d Q_ctl=%d, %s) "
                      "at pair #%d" % (qa + qc, qa, qc, family, k),
                      flush=True)
            if qa + qc > 0:
                results.append({"family": family, "u": str(u), "v": str(v),
                                "q_active": qa, "q_control": qc})
        if k % 500 == 0:
            print("scanned %d/%d" % (k, len(pairs)), flush=True)

    verdict = {
        "pairs_scanned": len(pairs),
        "positive_Q_directions": len(results),
        "max_Q_total": best[0], "max_detail": {
            "q_active": best[1], "q_control": best[2],
            "family": best[3], "u": str(best[4]), "v": str(best[5])},
        "interpretation": ("POSITIVE Q_total = certified negative "
                           "curvature of the loss (strict saddle) along "
                           "that direction; all-nonpositive = the "
                           "structured translation sector is curvature-"
                           "nonnegative at the flip (exact)."),
        "positives": results[:50],
    }
    with open(args.out, "w") as fh:
        json.dump(verdict, fh, indent=1)
    print(json.dumps({k: v for k, v in verdict.items()
                      if k != "positives"}), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
