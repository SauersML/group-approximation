"""Exact stationarity of the tensor flip for the stage-2 objective.

At W = I every syllable of a T_St word acts on C[G] (G = GL4(F2), 20160
points) as a two-sided translation: factor 1 -> L_g, factor 2 -> R_h
(the flip is absorbed in this role assignment, validated by the stage-2
baseline gates).  The directional derivative of the word defect along
anti-Hermitian X is a signed sum of traces tr(M_j X) with

    M_j = [R_{h_j}, D_j C_j] = L_{a_j} (R_{h_j b_j} - R_{b_j h_j}),

where C_j / D_j are the prefix/suffix products, a_j = (suffix L)(prefix
L) and b_j = (suffix R)(prefix R).  The Riemannian gradient of the
objective at the flip vanishes iff the antisymmetrization

    A = M - M^T,   M = sum of signed L_a R_c terms,

is the zero matrix.  Distinct pairs (a, c) give distinct permutation
operators (trivial center), but permutation matrices are linearly
dependent, so pair-level cancellation is sufficient, not necessary;
the decisive quantity is the exact integer

    ||A||_HS^2 = sum_{p,q} alpha_p alpha_q Fix(a_p^{-1} a_q, c_p^{-1} c_q),

with Fix(u, v) = |Centralizer(u)| if u ~ v in G else 0.  Conjugacy is
tested by the complete Frobenius invariant (ranks of f(u)^j over the
eight irreducible polynomials of degree <= 4 over F2); class sizes come
from bucketing all 20160 elements by that invariant.  Everything is
integer arithmetic — the verdict is exact, not floating point.
"""

import argparse
import json
import os
import sys
from collections import Counter, defaultdict

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_two_chart_search import gf2_inv, gf2_mul  # noqa: E402
from atlas_stabilizer_coset_search import (  # noqa: E402
    enumerate_group, matrix_key)
from atlas_true_criterion_stage2 import (  # noqa: E402
    I4, load_relators, factor_projections)

# irreducible polynomials over F2 of degree <= 4, low-to-high coeffs
IRREDUCIBLE = [
    (0, 1),            # x
    (1, 1),            # x + 1
    (1, 1, 1),         # x^2 + x + 1
    (1, 1, 0, 1),      # x^3 + x + 1
    (1, 0, 1, 1),      # x^3 + x^2 + 1
    (1, 1, 0, 0, 1),   # x^4 + x + 1
    (1, 0, 0, 1, 1),   # x^4 + x^3 + 1
    (1, 1, 1, 1, 1),   # x^4 + x^3 + x^2 + x + 1
]


def gf2_rank(matrix):
    rows = [int("".join(str(b) for b in row), 2) for row in matrix]
    rank = 0
    for bit in (8, 4, 2, 1):
        pivot = next((i for i in range(rank, 4) if rows[i] & bit), None)
        if pivot is None:
            continue
        rows[pivot], rows[rank] = rows[rank], rows[pivot]
        rows = [r ^ rows[rank] if i != rank and (r & bit) else r
                for i, r in enumerate(rows)]
        rank += 1
    return rank


def poly_eval(coeffs, powers):
    out = np.zeros((4, 4), dtype=np.uint8)
    for degree, bit in enumerate(coeffs):
        if bit:
            out ^= powers[degree]
    return out


class ConjugacyOracle:
    def __init__(self, elements):
        self.invariant_cache = {}
        buckets = Counter(self.invariant(m) for m in elements)
        order = len(elements)
        self.centralizer = {inv: order // size
                            for inv, size in buckets.items()}

    def invariant(self, matrix):
        key = matrix_key(matrix)
        if key not in self.invariant_cache:
            powers = [I4.copy()]
            for _ in range(4):
                powers.append(gf2_mul(powers[-1], matrix))
            ranks = []
            for coeffs in IRREDUCIBLE:
                value = poly_eval(coeffs, powers)
                accumulated = value
                for _ in range(4 // (len(coeffs) - 1)):
                    ranks.append(gf2_rank(accumulated))
                    accumulated = gf2_mul(accumulated, value)
            self.invariant_cache[key] = tuple(ranks)
        return self.invariant_cache[key]

    def fix(self, u, v):
        """# of x with u x v^{-1} = x, i.e. |C(u)| if u ~ v else 0."""
        iu, iv = self.invariant(u), self.invariant(v)
        return self.centralizer[iu] if iu == iv else 0


def word_terms(word, registry):
    """Signed (a, c) pairs of M for one word at W = I."""
    m = len(word)
    prefix_l, prefix_r = [I4.copy()], [I4.copy()]
    for factor, mat in word:
        prefix_l.append(gf2_mul(prefix_l[-1], mat)
                        if factor == 1 else prefix_l[-1])
        prefix_r.append(gf2_mul(prefix_r[-1], mat)
                        if factor == 2 else prefix_r[-1])
    suffix_l, suffix_r = [None] * (m + 1), [None] * (m + 1)
    suffix_l[m], suffix_r[m] = I4.copy(), I4.copy()
    for i in range(m - 1, -1, -1):
        factor, mat = word[i]
        suffix_l[i] = (gf2_mul(mat, suffix_l[i + 1])
                       if factor == 1 else suffix_l[i + 1])
        suffix_r[i] = (gf2_mul(mat, suffix_r[i + 1])
                       if factor == 2 else suffix_r[i + 1])
    # suffix products must multiply in increasing-i order: A_{j+1}...A_m
    # has L-part m_{j+1} m_{j+2} ... — rebuilt above right-to-left with
    # mat on the LEFT, which yields exactly that order.
    terms = []
    for j in range(m):
        factor, h = word[j]
        if factor != 2:
            continue
        a = gf2_mul(suffix_l[j + 1], prefix_l[j])
        b = gf2_mul(suffix_r[j + 1], prefix_r[j])
        hb, bh = gf2_mul(h, b), gf2_mul(b, h)
        if matrix_key(hb) == matrix_key(bh):
            continue  # commutator term vanishes identically
        for value in (a, hb, bh):
            registry.setdefault(matrix_key(value), value)
        terms.append((+1, matrix_key(a), matrix_key(hb)))
        terms.append((-1, matrix_key(a), matrix_key(bh)))
    return terms


def antisymmetrize(counter, key_to_matrix):
    """Coefficients of A = M - M^T on distinct L_a R_c operators."""
    alpha = Counter()
    for (ka, kc), coeff in counter.items():
        alpha[(ka, kc)] += coeff
        inv_a = gf2_inv(key_to_matrix[ka])
        inv_c = gf2_inv(key_to_matrix[kc])
        key_to_matrix.setdefault(matrix_key(inv_a), inv_a)
        key_to_matrix.setdefault(matrix_key(inv_c), inv_c)
        alpha[(matrix_key(inv_a), matrix_key(inv_c))] -= coeff
    return {pair: c for pair, c in alpha.items() if c != 0}


def exact_hs_norm_sq(alpha, key_to_matrix, oracle):
    pairs = list(alpha.items())
    total = 0
    for i, ((ka, kc), ci) in enumerate(pairs):
        ai, cci = key_to_matrix[ka], key_to_matrix[kc]
        ai_inv, ci_inv = gf2_inv(ai), gf2_inv(cci)
        for (kb, kd), cj in pairs[i:]:
            u = gf2_mul(ai_inv, key_to_matrix[kb])
            v = gf2_mul(ci_inv, key_to_matrix[kd])
            overlap = oracle.fix(u, v)
            if overlap:
                weight = ci * cj * overlap
                total += weight if kb == ka and kd == kc else 2 * weight
    return total


def analyse(name, words, oracle, key_to_matrix):
    counter = Counter()
    raw_terms = 0
    for _label, word in words:
        for sign, ka, kc in word_terms(word, key_to_matrix):
            counter[(ka, kc)] += sign
            raw_terms += 1
    counter = Counter({p: c for p, c in counter.items() if c != 0})
    alpha = antisymmetrize(counter, key_to_matrix)
    norm_sq = (exact_hs_norm_sq(alpha, key_to_matrix, oracle)
               if alpha else 0)
    report = {
        "slice": name,
        "words": len(words),
        "raw_terms": raw_terms,
        "distinct_pairs_in_M": len(counter),
        "surviving_pairs_in_A": len(alpha),
        "pair_level_cancellation": not alpha,
        "exact_hs_norm_sq_of_A": norm_sq,
        "stationary": norm_sq == 0,
    }
    print(json.dumps(report), flush=True)
    return report, counter, alpha


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("list_json")
    parser.add_argument("--out", default="atlas-flip-stationarity.json")
    args = parser.parse_args()

    words = load_relators(args.list_json)
    active, control = [], []
    for name, word in words:
        p1, p2 = factor_projections(word)
        if (not np.array_equal(p1, I4)) or (not np.array_equal(p2, I4)):
            active.append((name, word))
        else:
            control.append((name, word))
    print("words: %d active, %d control" % (len(active), len(control)),
          flush=True)

    elements, _ = enumerate_group()
    oracle = ConjugacyOracle(elements)
    print("conjugacy oracle: %d classes over %d elements"
          % (len(oracle.centralizer), len(elements)), flush=True)

    key_to_matrix = {}
    rep_a, cnt_a, alf_a = analyse("active", active, oracle, key_to_matrix)
    rep_c, cnt_c, alf_c = analyse("control", control, oracle, key_to_matrix)
    combined = Counter(cnt_a)
    combined.update(cnt_c)
    alpha_t = antisymmetrize(combined, key_to_matrix)
    norm_t = (exact_hs_norm_sq(alpha_t, key_to_matrix, oracle)
              if alpha_t else 0)
    rep_t = {"slice": "combined (equal weights, as the run's objective)",
             "surviving_pairs_in_A": len(alpha_t),
             "exact_hs_norm_sq_of_A": norm_t,
             "stationary": norm_t == 0}
    print(json.dumps(rep_t), flush=True)

    # the run's Riemannian gradient norm at W = I would be
    # (2 / (n * 72)) * sqrt(||A_combined||^2); report for comparison
    n = len(elements)
    predicted = (2.0 / (n * 72)) * (norm_t ** 0.5)
    print("predicted Riemannian grad norm at W=I: %.6e" % predicted,
          flush=True)

    with open(args.out, "w") as handle:
        json.dump({"active": rep_a, "control": rep_c, "combined": rep_t,
                   "predicted_riemannian_grad_norm": predicted}, handle,
                  indent=1)
    print("wrote", args.out, flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
