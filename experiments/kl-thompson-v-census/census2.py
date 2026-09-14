"""Census of nonsingular one-variable words over Thompson's V for the KL collapse test.

Words are cyclic sequences of syllables  g_0 t^(e_0) g_1 t^(e_1) ... g_(n-1) t^(e_(n-1)),
with e_i = +-1 (powers split), coefficient g_i in {1, a, b, B, c} (Bleak--Quick generators;
B = b^-1), and g_i != 1 at opposite-sign corners (cyclic reduction).  The corner of g_i sits
between t^(e_(i-1)) and t^(e_i).

Kept: variable length n in LENGTHS, degree m = sum e_i with 0 < m < n (one-sign words are
covered by Levin's positive-equation theorem; m < 0 is equivalent under t -> t^-1).

Filters (each justified by a landed theorem, as named on main):
  finite  -- coefficient support inside <a,b> (order 24), <a,c> (order 6) or <b,c> (order 60),
             orders computed exactly with vgroup.py: the coefficient subgroup is
             finite, hence hyperlinear, and a KL failure localizes to the coefficient subgroup
             (kl-failure-localizes-to-the-coefficient-subgroup, kervaire-laudenbach-holds-for-hyperlinear).
  r>=4    -- at least four light same-sign corners (kl-four-same-sign-corner-words-inject, item 1).
Canonical representative: minimum over rotations of w and of sigma(w^-1), sigma: t <-> t^-1,
both of which preserve the degree and the normal closure up to an automorphism of V * <t>.
Output lines: "<id> <word> n=<n> m=<m> r=<r>".
"""
import sys
from itertools import product

LETTERS = ["a", "b", "B", "c"]
INV = {"a": "a", "b": "B", "B": "b", "c": "c", "1": "1", "t": "T", "T": "t"}


def word_string(signs, coeffs):
    return "".join(("" if g == "1" else g) + ("t" if e > 0 else "T") for g, e in zip(coeffs, signs))


def sigma_inverse(signs, coeffs):
    # w^-1 = t^(-e_(n-1)) g_(n-1)^-1 ... t^(-e_0) g_0^-1 ; sigma flips signs back.
    # As a cyclic syllable list (coefficient before each t-letter):
    n = len(signs)
    new_signs = []
    new_coeffs = []
    for k in range(n - 1, -1, -1):
        # letter t^(-e_k) preceded (cyclically) by g_(k+1)^-1
        new_signs.append(signs[k])  # sigma(-e_k) = e_k
        new_coeffs.append(INV[coeffs[(k + 1) % n]])
    return new_signs, new_coeffs


def rotations(signs, coeffs):
    n = len(signs)
    for i in range(n):
        yield tuple(signs[i:] + signs[:i]), tuple(coeffs[i:] + coeffs[:i])


def canonical(signs, coeffs):
    best = None
    s2, c2 = sigma_inverse(list(signs), list(coeffs))
    for s, c in list(rotations(list(signs), list(coeffs))) + list(rotations(s2, c2)):
        key = word_string(s, c)
        if best is None or key < best:
            best = key
    return best


def light_corners(signs, coeffs):
    n = len(signs)
    corners = []  # (type, label) for same-sign corners
    for i in range(n):
        prev, cur = signs[i - 1], signs[i]
        if prev == cur:
            corners.append(("P" if cur > 0 else "N", coeffs[i]))
    r = 0
    for idx, (typ, lab) in enumerate(corners):
        heavy = False
        for jdx, (typ2, lab2) in enumerate(corners):
            if jdx == idx:
                continue
            if typ2 == typ and lab2 == lab:
                heavy = True
            if typ2 != typ and lab2 == INV[lab]:
                heavy = True
        if not heavy:
            r += 1
    return r


def main(lengths, outpath):
    stats = {}
    seen = set()
    idx = 0
    with open(outpath, "w") as out:
        for n in lengths:
            for signs in product([1, -1], repeat=n):
                m = sum(signs)
                if not (0 < m < n):
                    continue
                choices = [(["1"] + LETTERS) if signs[i - 1] == signs[i] else LETTERS for i in range(n)]
                for coeffs in product(*choices):
                    key = canonical(signs, coeffs)
                    if key in seen:
                        continue
                    seen.add(key)
                    st = stats.setdefault((n, m), {"classes": 0, "finite": 0, "r>=4": 0, "kept": 0})
                    st["classes"] += 1
                    support = {g for g in coeffs if g != "1"}
                    if support <= {"a", "b", "B"} or support <= {"a", "c"} or support <= {"b", "B", "c"}:
                        st["finite"] += 1
                        continue
                    r = light_corners(signs, coeffs)
                    if r >= 4:
                        st["r>=4"] += 1
                        continue
                    st["kept"] += 1
                    out.write(f"{idx} {key} n={n} m={m} r={r}\n")
                    idx += 1
    for k in sorted(stats):
        print(k, stats[k])
    print("total kept", idx)


if __name__ == "__main__":
    lengths = [int(x) for x in sys.argv[1].split(",")] if len(sys.argv) > 1 else [6, 7]
    main(lengths, sys.argv[2] if len(sys.argv) > 2 else "survivors67.txt")
