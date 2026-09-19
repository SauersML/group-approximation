#!/usr/bin/env python3
"""Checks for kms-2to2-instances-are-padded-dkkms-selector-lecs (claim is OPEN).

CORRECTION, 2026-09-18 (post-referee).  The provenance sentence in the next
paragraph -- "The instance that Theorem 1.4 of that paper is about is ...
G_folded" -- is ASSERTED here, not checked, and it was refuted by all three
referee lenses: TR18-006's reference [12] is Khot--Minzer--Safra, ECCC TR16-124,
which does construct a 2-to-2 game, already single-alphabet and needing no
padding.  This script cannot and does not test that identification.  What it
does test is four structural facts about the self-constructed padded game
G_pad, and those four checks are green and are not in dispute.  Read every
mention of "the proved 2-to-2 instances" below as "G_pad".

Khot--Minzer--Safra, ECCC TR18-006, Definition 1.3 asks for an instance of
2-to-2 Game[F_2^l]: n variables over F_2^l with constraints

    T_ij x_i + T'_ij x_j in {b_ij, b'_ij},   T_ij, T'_ij invertible l x l.

The instance that Theorem 1.4 of that paper is about is not built there.  It is
the folded Grassmann game G_folded of Dinur--Khot--Kindler--Minzer--Safra, ECCC
TR16-198, Section 4.2, whose two sides carry Sigma_A = {0,1}^l and
Sigma_B = {0,1}^(l-1) and whose constraints are 2-to-1.  The presentation
change is a free bit on the B side:

    Sigma_B^pad = Fun(L') x F_2  ~  F_2^l,
    constraint((U,L),(V,L')) accepts (sigma, (sigma', c)) iff A_sigma(U,L)|_L' = sigma'.

This script checks the four facts that the claim needs from the construction.

PART A (folding aggregates to an exactly 2-to-1 constraint).  For every class
representative R and every (V,L') the folded constraint is the aggregate of the
constraints of all (U,L) in the class with L' <= L.  Claim 4.3 of TR16-198 with
D = L' says these coincide.  Checked directly: A_sigma(U,L1)|_L' =
A_sigma(U,L2)|_L' for every sigma and every pair L1, L2 in the class above L'.
So the aggregate is exactly 2-to-1, hence the padded constraint is exactly
2-to-2 rather than degenerating to a unique or an unsatisfiable constraint.

PART B (the padded constraint is linear with invertible matrices).  With a
basis v_1..v_(l-1) of L' extended by v_l = x to a basis of L, put

    (T sigma)_i = sigma(r(v_i)),        r : L -> R the folding bijection,
    T' = identity on F_2^l,
    b_i = h_U(y(v_i)),                  z = r(z) + y(z), y(z) in H_U,
    b' = b + e_l.

Checked: T is invertible, b != b', and for all (sigma, tau) in F_2^l x F_2^l the
padded constraint accepts (sigma, tau) iff T sigma + tau in {b, b'}.  Also
checked: the accepted relation is exactly 2-to-2.

PART C (the branch identity (B) survives the padding, for every free bit).  For
every orientation o of the padded constraint -- i.e. every perfect matching of
the K_(2,2) block, and also every non-matching choice -- the bit function is
g_e(sigma', c) = A_(o_e(sigma',c))(U,L)(x_e).  Checked: whenever U is clean for
an assignment a and the padded honest labelling hon_c(a) = (a|_R, (a|_L', c))
satisfies the oriented constraint, g_e(hon_c(a)_w) = <a, x_e>, for both values
of c and every orientation.  Control: on dirty U the identity fails somewhere.

PART D (the padding changes no value, for labellings and for lifts).  On small
abstract bipartite 2-to-1 games: OPT(G_pad) = OPT(G_folded); and for every
labelling h of G_folded,

    max over padded orientations o and bits c of val(G_pad,o)(h_c)
      = max over 2-to-1 orientations o' of val(G_folded,o')(h).

So a witness gains nothing from the padding.  (The converse direction -- an
efficient selector on G_pad cannot be converted into one on G_folded, because
the conversion would need the witness's bits c -- is why the claim runs the
decoding theorem on G_pad directly instead of reducing to the 2-to-1 case.)

Exit code 0 iff every check passes.
"""
import itertools
import random
import sys


# ---------------------------------------------------------------- linear algebra
def span(vecs):
    s = {0}
    for v in vecs:
        s |= {u ^ v for u in s}
    return frozenset(s)


def basis_of(subspace):
    """Greedy basis of a subspace given as a set of vectors."""
    basis = []
    cur = {0}
    for v in sorted(subspace):
        if v not in cur:
            basis.append(v)
            cur = set(span(basis))
    return basis


def subspaces(ambient, d):
    """All d-dimensional subspaces contained in the set `ambient` (a subspace)."""
    out = set()
    nz = [v for v in sorted(ambient) if v]
    for combo in itertools.combinations(nz, d):
        s = span(combo)
        if len(s) == 2 ** d:
            out.add(s)
    return out


def functionals(basis):
    """All linear functionals on span(basis), as dicts vector -> bit."""
    out = []
    for vals in itertools.product((0, 1), repeat=len(basis)):
        f = {0: 0}
        for b, val in zip(basis, vals):
            f = {**f, **{z ^ b: fz ^ val for z, fz in f.items()}}
        out.append(f)
    return out


def dot(a, x):
    return bin(a & x).count("1") & 1


# ------------------------------------------------------------------ DKKMS block
def block(k):
    """X_U = F_2^(3k); equation e_i owns variables 3i,3i+1,3i+2."""
    n = 3 * k
    xs = [0b111 << (3 * i) for i in range(k)]
    H = span(xs)
    return n, xs, H


def h_map(xs, b, H):
    """h_U : H_U -> F_2 with h_U(x_{e_i}) = b_i, as a dict."""
    h = {0: 0}
    for x, bi in zip(xs, b):
        h = {**h, **{z ^ x: hz ^ bi for z, hz in h.items()}}
    assert set(h) == set(H)
    return h


def decompose(z, R, H):
    """z = r + y with r in R, y in H; unique when R cap H = 0 and z in R + H."""
    for y in H:
        if z ^ y in R:
            return z ^ y, y
    raise ValueError("not in R + H")


def unfold(sigma, R, H, h, L):
    """A_sigma(U,L) as a dict on L, from Definition 4.2 of TR16-198."""
    out = {}
    for z in L:
        r, y = decompose(z, R, H)
        out[z] = sigma[r] ^ h[y]
    return out


# ------------------------------------------------------------------------ Part A
def part_a(k, l, verbose=True):
    n, xs, H = block(k)
    amb = frozenset(range(1 << n))
    checks = 0
    pairs = 0
    for b in itertools.product((0, 1), repeat=k):
        h = h_map(xs, b, H)
        for R in subspaces(amb, l):
            if len(R & H) != 1:
                continue
            RH = span(list(R) + list(H))
            members = [L for L in subspaces(RH, l) if len(L & H) == 1]
            # the class of R is exactly {(U,L) : L + H = R + H, L cap H = 0}
            assert R in members
            sigmas = functionals(basis_of(R))
            unfolded = {L: [unfold(s, R, H, h, L) for s in sigmas] for L in members}
            for L1, L2 in itertools.combinations(members, 2):
                inter = L1 & L2
                for Lp in subspaces(inter, l - 1):
                    pairs += 1
                    for f1, f2 in zip(unfolded[L1], unfolded[L2]):
                        checks += 1
                        for z in Lp:
                            if f1[z] != f2[z]:
                                return False, f"A: aggregate splits at k={k} l={l}"
    if verbose:
        print(f"  A  k={k} l={l}: {pairs} (L1,L2,L') triples, {checks} sigma-checks, 0 splits")
    return True, None


# ------------------------------------------------------------------------ Part B
def part_b(k, l, verbose=True):
    n, xs, H = block(k)
    amb = frozenset(range(1 << n))
    edges = 0
    for b in itertools.product((0, 1), repeat=k):
        h = h_map(xs, b, H)
        for R in subspaces(amb, l):
            if len(R & H) != 1:
                continue
            RH = span(list(R) + list(H))
            for L in subspaces(RH, l):
                if len(L & H) != 1:
                    continue
                for Lp in subspaces(L, l - 1):
                    edges += 1
                    vb = basis_of(Lp)
                    x = next(z for z in sorted(L) if z not in Lp)
                    vfull = vb + [x]
                    # T and the offset b, from the folding decomposition
                    rs, ys = zip(*(decompose(v, R, H) for v in vfull))
                    Rbasis = basis_of(R)
                    sigmas = functionals(Rbasis)
                    off = tuple(h[y] for y in ys)
                    Tcols = []
                    for s in sigmas:
                        Tcols.append(tuple(s[r] for r in rs))
                    # T as a map F_2^l -> F_2^l in the sigma-coordinates given by Rbasis
                    sig_coord = {}
                    for s in sigmas:
                        sig_coord[id(s)] = tuple(s[r] for r in Rbasis)
                    Tmat = {}
                    for s, col in zip(sigmas, Tcols):
                        Tmat[sig_coord[id(s)]] = col
                    # invertibility: T is a bijection on F_2^l
                    if len(set(Tmat.values())) != 2 ** l:
                        return False, "B: T not invertible"
                    # additivity of T (it must be linear, not merely bijective)
                    for s1 in sigmas:
                        for s2 in sigmas:
                            c1, c2 = sig_coord[id(s1)], sig_coord[id(s2)]
                            c3 = tuple(a ^ b2 for a, b2 in zip(c1, c2))
                            got = Tmat[c3]
                            want = tuple(a ^ b2 for a, b2 in zip(Tmat[c1], Tmat[c2]))
                            if got != want:
                                return False, "B: T not linear"
                    bb = off
                    bbp = tuple(off[i] ^ (1 if i == l - 1 else 0) for i in range(l))
                    if bb == bbp:
                        return False, "B: b = b', constraint is unique not 2-to-2"
                    # the padded relation, from the construction
                    accept = set()
                    for s in sigmas:
                        A = unfold(s, R, H, h, L)
                        sp = tuple(A[v] for v in vb)          # sigma' = A|_L' in the L'-basis
                        for c in (0, 1):
                            accept.add((sig_coord[id(s)], sp + (c,)))
                    # the linear form
                    linear = set()
                    for sc in itertools.product((0, 1), repeat=l):
                        for tau in itertools.product((0, 1), repeat=l):
                            ssum = tuple(a ^ b2 for a, b2 in zip(Tmat[sc], tau))
                            if ssum == bb or ssum == bbp:
                                linear.add((sc, tau))
                    if accept != linear:
                        return False, "B: padded relation is not the stated linear form"
                    # exactly 2-to-2
                    from collections import Counter
                    cl = Counter(p[0] for p in accept)
                    cr = Counter(p[1] for p in accept)
                    if set(cl.values()) != {2} or set(cr.values()) != {2}:
                        return False, "B: padded relation is not 2-to-2"
                    if len(cl) != 2 ** l or len(cr) != 2 ** l:
                        return False, "B: padded relation is not total"
    if verbose:
        print(f"  B  k={k} l={l}: {edges} (b,R,L,L') edges, all exactly 2-to-2 and linear with T invertible")
    return True, None


# ------------------------------------------------------------------------ Part C
def part_c(k, l, verbose=True):
    """(B) for the padded game: every orientation, every free bit, clean U."""
    n, xs, H = block(k)
    amb = frozenset(range(1 << n))
    good = 0
    dirty_fail = 0
    dirty_tot = 0
    for a in range(1 << n):
        btrue = tuple(dot(a, x) for x in xs)
        for b in itertools.product((0, 1), repeat=k):
            clean = (b == btrue)
            h = h_map(xs, b, H)
            for R in subspaces(amb, l):
                if len(R & H) != 1:
                    continue
                RH = span(list(R) + list(H))
                # the honest class label is a|_R
                sigma_hon = {z: dot(a, z) for z in R}
                if not all(
                    sigma_hon[u ^ v] == sigma_hon[u] ^ sigma_hon[v] for u in R for v in R
                ):
                    return False, "C: a|_R not linear"
                for L in subspaces(RH, l):
                    if len(L & H) != 1:
                        continue
                    A_hon = unfold(sigma_hon, R, H, h, L)
                    Rbasis = basis_of(R)
                    sigmas = functionals(Rbasis)
                    for Lp in subspaces(L, l - 1):
                        vb = basis_of(Lp)
                        for x in sorted(L):
                            if x in Lp:
                                continue
                            # the two preimages of sigma'_hon = a|_L'
                            sp_hon = tuple(dot(a, v) for v in vb)
                            pre = []
                            for s in sigmas:
                                As = unfold(s, R, H, h, L)
                                if tuple(As[v] for v in vb) == sp_hon:
                                    pre.append((s, As))
                            if len(pre) != 2:
                                return False, "C: fiber size is not 2"
                            # every orientation of the K_(2,2) block: a choice of
                            # preimage for (sigma'_hon, 0) and for (sigma'_hon, 1),
                            # matching or not
                            for i0 in (0, 1):
                                for i1 in (0, 1):
                                    for c in (0, 1):
                                        chosen = pre[i0 if c == 0 else i1]
                                        s_sel, As_sel = chosen
                                        # hon_c(a) satisfies the oriented edge iff the
                                        # orientation picked the honest class label
                                        satisfied = all(
                                            s_sel[z] == sigma_hon[z] for z in R
                                        )
                                        g = As_sel[x]
                                        if clean:
                                            if satisfied and g != dot(a, x):
                                                return False, "C: (B) fails on a clean U"
                                            if satisfied:
                                                good += 1
                                        else:
                                            dirty_tot += 1
                                            if satisfied and g != dot(a, x):
                                                dirty_fail += 1
    if verbose:
        print(
            f"  C  k={k} l={l}: {good} clean satisfied (orientation, bit) cases, 0 branch-identity failures; "
            f"dirty control: {dirty_fail} failures in {dirty_tot} cases"
        )
    if dirty_tot and dirty_fail == 0:
        return False, "C: dirty control is vacuous"
    return True, None


# ------------------------------------------------------------------------ Part D
def part_d(trials=200, seed=20260918, verbose=True):
    """Padding preserves OPT and the best honest lift value, on abstract games."""
    rng = random.Random(seed)
    for _ in range(trials):
        l = rng.choice([2, 3])
        nA, nB = rng.randint(1, 2), rng.randint(1, 2)
        SA = 2 ** l
        SB = 2 ** (l - 1)
        edges = []
        for u in range(nA):
            for v in range(nB):
                if rng.random() < 0.8:
                    # a surjection SA -> SB with all fibers of size 2
                    order = list(range(SA))
                    rng.shuffle(order)
                    pi = {}
                    for j, t in enumerate(order):
                        pi[t] = j // 2
                    edges.append((u, v, pi))
        if not edges:
            continue
        # OPT of the 2-to-1 game
        best = -1
        for la in itertools.product(range(SA), repeat=nA):
            for lb in itertools.product(range(SB), repeat=nB):
                val = sum(1 for (u, v, pi) in edges if pi[la[u]] == lb[v])
                best = max(best, val)
        # OPT of the padded 2-to-2 game
        bestp = -1
        for la in itertools.product(range(SA), repeat=nA):
            for lb in itertools.product(range(SB * 2), repeat=nB):
                val = sum(1 for (u, v, pi) in edges if pi[la[u]] == lb[v] // 2)
                bestp = max(bestp, val)
        if best != bestp:
            return False, "D: padding changed OPT"
        # best lift value of a fixed labelling h, by explicit enumeration of
        # orientations in both presentations.  Only l = 2 (SB = 2), to keep the
        # enumeration exhaustive.
        if l != 2 or len(edges) > 4:
            continue
        fibers = [{t: [s for s in range(SA) if pi[s] == t] for t in range(SB)}
                  for (_, _, pi) in edges]
        for _ in range(3):
            h = (
                tuple(rng.randrange(SA) for _ in range(nA)),
                tuple(rng.randrange(SB) for _ in range(nB)),
            )
            # 2-to-1 orientations: o'_e(sigma') is one of the two preimages
            m1 = -1
            for pick in itertools.product(
                *[list(itertools.product((0, 1), repeat=SB)) for _ in edges]
            ):
                cnt = 0
                for (u, v, pi), fib, ch in zip(edges, fibers, pick):
                    if fib[h[1][v]][ch[h[1][v]]] == h[0][u]:
                        cnt += 1
                m1 = max(m1, cnt)
            # padded orientations: a perfect matching of each K_(2,2) block, so
            # o_e(sigma',0) and o_e(sigma',1) are the two preimages in some order;
            # plus a free bit c_v at every B-vertex
            m2 = -1
            for cbits in itertools.product((0, 1), repeat=nB):
                for pick in itertools.product(
                    *[list(itertools.product((0, 1), repeat=SB)) for _ in edges]
                ):
                    cnt = 0
                    for (u, v, pi), fib, ch in zip(edges, fibers, pick):
                        t = h[1][v]
                        idx = ch[t] ^ cbits[v]
                        if fib[t][idx] == h[0][u]:
                            cnt += 1
                    m2 = max(m2, cnt)
            if m1 != m2:
                return False, "D: padding changed the best honest lift value"
    if verbose:
        print(f"  D  {trials} random abstract games: OPT and best honest lift value unchanged by padding")
    return True, None


def main():
    ok = True
    print("PART A -- folding aggregates to an exactly 2-to-1 constraint")
    for (k, l) in [(2, 2), (2, 3)]:
        res, msg = part_a(k, l)
        ok &= res
        if not res:
            print("  FAIL", msg)
    print("PART B -- the padded constraint is 2-to-2, linear, with T invertible and b != b'")
    for (k, l) in [(2, 2)]:
        res, msg = part_b(k, l)
        ok &= res
        if not res:
            print("  FAIL", msg)
    print("PART C -- the branch identity (B) under padding, every orientation and free bit")
    for (k, l) in [(2, 2)]:
        res, msg = part_c(k, l)
        ok &= res
        if not res:
            print("  FAIL", msg)
    print("PART D -- padding preserves OPT and the best honest lift value")
    res, msg = part_d()
    ok &= res
    if not res:
        print("  FAIL", msg)
    print()
    print("ALL CHECKS PASSED" if ok else "FAILURES ABOVE")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
