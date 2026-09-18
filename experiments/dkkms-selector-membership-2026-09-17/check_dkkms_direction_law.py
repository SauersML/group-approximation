#!/usr/bin/env python3
"""Checks for dkkms-2to1-instances-satisfy-selector-decoding-hypotheses.

Model of one DKKMS block (ECCC TR16-198, Section 4.2).  U = (e_1..e_k) with
disjoint equations; variable 3i+j (j=0,1,2) is the j-th variable of e_i, so
X_U = F_2^{3k} and x_{e_i} = 0b111 << 3i.  H_U = Span(x_e).  V keeps e_i or
replaces it by one of its variables.  X_V = vectors supported on V.

Part A (direction law).  For each (V, L') with L' in Gr(X_V, l-1), enumerate
every L in Gr(X_U, l) with L' <= L and L cap H_U = 0 (the vertices of A), take
L uniform among them and x_e uniform in L minus L'.  Check:
  A1. valid supersets exist iff L' cap H_U = 0, and then their number is
      (2^{3k} - 2^{l-1+k}) / 2^{l-1};
  A2. the law of x_e is exactly uniform on X_U minus (L' + H_U);
  A3. its total variation from uniform on F_2^{3k} is 2^{l-1-2k};
  A4. Pr_{L'}[L' cap H_U = 0 | V] depends on V only through the number t of
      kept equations (so the U-marginal of the edge law is uniform: K = 1).
Exhaustive over all V and L' for (k,l) in {(2,2),(2,3)}; random (V, L') for
(3,2),(3,3),(4,2).

Part B (unfolding and branch identity), exhaustive for k=2, l=2 and sampled
for k=3, l=2.  For all right-hand sides b, all assignments a in F_2^{3k}, all
R, L in Gr(X_U, l) avoiding H_U with L + H_U = R + H_U, and all L' <= L of
dimension l-1:
  B1. unfolding sigma -> (H_U,h_U)-extension restricted to L is a bijection
      Fun(R) -> Fun(L), so each multi-edge constraint is exactly 2-to-1;
  B2. the two preimages of any sigma' differ at every x in L minus L' (the
      orientation bit at any direction determines the branch: (B+));
  B3. if a satisfies every equation of U (a clean U), the unfolding of a|_R
      is a|_L, so the branch bit of hon(a) at x is <a, x> = <lambda_U, x>.
  Control: for dirty U, B3 fails for some (R, L, x); counted and reported.
"""
import itertools
import random
import sys
from fractions import Fraction


def dot(a, x):
    return bin(a & x).count("1") & 1


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {u ^ v for u in s}
    return frozenset(s)


def subspaces_of(ambient_vecs, d):
    """All d-dim subspaces spanned by vectors from a list (the list spans the ambient)."""
    out = set()
    nz = [v for v in ambient_vecs if v]
    for combo in itertools.combinations(nz, d):
        s = span(combo)
        if len(s) == 2 ** d:
            out.add(s)
    return out


def xv_vectors(k, choice):
    """choice[i] = 3 (keep equation) or j in {0,1,2} (keep variable 3i+j)."""
    mask = 0
    for i, c in enumerate(choice):
        mask |= (0b111 << 3 * i) if c == 3 else (1 << (3 * i + c))
    return [v for v in range(2 ** (3 * k)) if v & ~mask == 0]


def hu(k):
    return span([0b111 << 3 * i for i in range(k)])


# ---------------------------------------------------------------- Part A


def direction_law(k, l, choice, Lp, H):
    """Return (failures, tv) for one (V, L')."""
    fails = 0
    N = 2 ** (3 * k)
    LH = frozenset(u ^ h for u in Lp for h in H)
    meets = len(LH) != len(Lp) * len(H)
    supersets = set()
    for x in range(N):
        if x in Lp:
            continue
        L = frozenset(Lp | {u ^ x for u in Lp})
        if L & H == {0}:
            supersets.add(L)
    if meets:
        return (0 if not supersets else 1), None
    expect = Fraction(N - 2 ** (l - 1 + k), 2 ** (l - 1))
    if len(supersets) != expect:
        fails += 1
    law = {}
    w = Fraction(1, len(supersets) * 2 ** (l - 1))
    for L in supersets:
        for x in L - Lp:
            law[x] = law.get(x, 0) + w
    comp = [x for x in range(N) if x not in LH]
    u = Fraction(1, len(comp))
    if set(law) != set(comp) or any(law[x] != u for x in comp):
        fails += 1
    tv = sum(abs(law.get(x, 0) - Fraction(1, N)) for x in range(N)) / 2
    if tv != Fraction(2 ** (l - 1 + k), N):
        fails += 1
    return fails, tv


def part_a(k, l, rng=None, samples=None):
    H = hu(k)
    fails = 0
    checked = 0
    by_t = {}
    choices = list(itertools.product(range(4), repeat=k))
    if samples is None:
        for choice in choices:
            xv = xv_vectors(k, choice)
            grs = subspaces_of(xv, l - 1)
            good = 0
            for Lp in grs:
                f, tv = direction_law(k, l, choice, Lp, H)
                fails += f
                checked += 1
                good += tv is not None
            t = sum(1 for c in choice if c == 3)
            by_t.setdefault(t, set()).add(Fraction(good, len(grs)))
        a4 = all(len(s) == 1 for s in by_t.values())
        if not a4:
            fails += 1
    else:
        for _ in range(samples):
            choice = tuple(rng.randrange(4) for _ in range(k))
            xv = xv_vectors(k, choice)
            while True:
                gens = [rng.choice(xv) for _ in range(l - 1)]
                Lp = span(gens)
                if len(Lp) == 2 ** (l - 1):
                    break
            f, tv = direction_law(k, l, choice, Lp, H)
            fails += f
            checked += 1
        a4 = None
    print(f"Part A k={k} l={l}: (V,L') checked={checked} failures={fails}"
          f" tau=2^(l-1-2k)={Fraction(2 ** (l - 1 + k), 2 ** (3 * k))}"
          + ("" if a4 is None else f" A4 uniform-in-t={a4}"))
    return fails


# ---------------------------------------------------------------- Part B


def unfold_table(k, R, H, b):
    """Map c -> unfolding of sigma = <c,.>|_R as a dict z -> value on R + H."""
    basisH = [0b111 << 3 * i for i in range(k)]
    hval = {}
    for bits in itertools.product((0, 1), repeat=k):
        y = 0
        v = 0
        for i, t in enumerate(bits):
            if t:
                y ^= basisH[i]
                v ^= b[i]
        hval[y] = v
    decomp = {}
    for r in R:
        for y in H:
            decomp[r ^ y] = (r, y)
    return hval, decomp


def unfold(c, L, hval, decomp):
    return tuple(dot(c, decomp[z][0]) ^ hval[decomp[z][1]] for z in sorted(L))


def part_b(k, l, rng=None, samples=None):
    N = 2 ** (3 * k)
    H = hu(k)
    fails = 0
    clean_checks = 0
    dirty_mismatch = 0
    dirty_pairs = 0
    if samples is None:
        avoid = [S for S in subspaces_of(list(range(N)), l) if S & H == {0}]
        groups = {}
        for S in avoid:
            W = frozenset(u ^ h for u in S for h in H)
            groups.setdefault(W, []).append(S)
        pairs = [(R, L) for g in groups.values() for R in g for L in g]
    else:
        pairs = []
        while len(pairs) < samples:
            gens = [rng.randrange(N) for _ in range(l)]
            R = span(gens)
            if len(R) != 2 ** l or R & H != {0}:
                continue
            # L = graph of a random linear map R -> H over a basis of R
            basis = []
            for v in sorted(R):
                if v and len(span(basis + [v])) > len(span(basis)):
                    basis.append(v)
            Hl = sorted(H)
            L = span([v ^ rng.choice(Hl) for v in basis])
            if len(L) == 2 ** l and L & H == {0}:
                pairs.append((R, L))
    cs = list(range(N))
    for (R, L) in pairs:
        for b in itertools.product((0, 1), repeat=k):
            hval, decomp = unfold_table(k, R, H, b)
            funs_R = {}
            for c in cs:
                key = tuple(dot(c, r) for r in sorted(R))
                funs_R.setdefault(key, c)
            imgs = {unfold(c, L, hval, decomp) for c in funs_R.values()}
            if len(funs_R) != 2 ** l or len(imgs) != 2 ** l:
                fails += 1  # B1
            Ls = sorted(L)
            for Lp in subspaces_of(Ls, l - 1):
                fib = {}
                for c in funs_R.values():
                    t = unfold(c, L, hval, decomp)
                    val = dict(zip(Ls, t))
                    key = tuple(val[z] for z in sorted(Lp))
                    fib.setdefault(key, []).append(val)
                for vs in fib.values():
                    if len(vs) != 2 or any(vs[0][x] == vs[1][x] for x in L - Lp):
                        fails += 1  # B2
        for a in (range(N) if samples is None else [rng.randrange(N) for _ in range(4)]):
            clean = tuple(dot(a, 0b111 << 3 * i) for i in range(k))
            for b in itertools.product((0, 1), repeat=k):
                hval, decomp = unfold_table(k, R, H, b)
                got = unfold(a, L, hval, decomp)
                want = tuple(dot(a, z) for z in sorted(L))
                if b == clean:
                    clean_checks += 1
                    if got != want:
                        fails += 1  # B3
                else:
                    dirty_pairs += 1
                    dirty_mismatch += got != want
    print(f"Part B k={k} l={l}: pairs={len(pairs)} clean-checks={clean_checks}"
          f" failures={fails}; control dirty-U mismatches={dirty_mismatch}/{dirty_pairs}")
    return fails


def main():
    rng = random.Random(20260917 if len(sys.argv) < 2 else int(sys.argv[1]))
    f = 0
    f += part_a(2, 2)
    f += part_a(2, 3)
    f += part_a(3, 2, rng, 60)
    f += part_a(3, 3, rng, 30)
    f += part_a(4, 2, rng, 6)
    f += part_b(2, 2)
    f += part_b(3, 2, rng, 40)
    print("TOTAL FAILURES", f)
    return 1 if f else 0


if __name__ == "__main__":
    sys.exit(main())
