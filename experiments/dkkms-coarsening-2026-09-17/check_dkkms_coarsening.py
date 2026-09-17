#!/usr/bin/env python3
"""Brute-force check for grassmann-composed-2to2-coarsenings-are-satisfiable.

Builds a small folded DKKMS instance (Dinur--Khot--Kindler--Minzer--Safra,
ECCC TR16-198, Section 4.2) from an UNSATISFIABLE 3LIN instance, with k = 2
and l = 2 (option --l 3), and checks:

  (a) DKKMS Lemma 4.1 at dimension l and at every dimension m < l: every
      folding class C has a member (U, R) with L + H_U = R + H_U for all
      members (U, L) of C;
  (b) R_Q meets H_U + H_U' only in 0 for all members U, U' of its class;
  (c) on the derived 2-to-2 edges (two A-neighbours of one B-vertex (V, L')),
      a pair of view subspaces (M1, M2) is exact iff M_i = r_i(N) for one
      N <= L' (brute force over the affine constraint space H_e);
  (d) the gauge labelling F(C, M)(r) = h_U(r - pi_Q(r)) is well defined
      (independent of the member U used) and satisfies every exact triple,
      so the coarsening Can has value 1 although the 3LIN instance is
      unsatisfiable;
  (e) control: the all-zero labelling violates some exact triples, so the
      offsets are genuinely present.

Vectors of F_2^n are int bitmasks.
"""
import argparse
import itertools
import random
import sys


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return frozenset(s)


def dim_of(sp):
    return len(sp).bit_length() - 1


def vec(vars_):
    v = 0
    for i in vars_:
        v |= 1 << i
    return v


def make_instance(rng, n, m_eq):
    """3LIN on n variables: an even cover {01 2, 0 3 4, 1 3 5, 2 4 5} with odd
    right-hand side (so unsatisfiable) plus random equations; two equations
    share at most one variable."""
    eqs = [(0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5)]
    tries = 0
    while len(eqs) < m_eq and tries < 10000:
        tries += 1
        e = tuple(sorted(rng.sample(range(n), 3)))
        if all(len(set(e) & set(f)) <= 1 for f in eqs):
            eqs.append(e)
    b = [rng.randrange(2) for _ in eqs]
    b[3] = b[0] ^ b[1] ^ b[2] ^ 1
    return eqs, b


def unsatisfiable(n, eqs, b):
    for a in range(1 << n):
        if all(((a >> e[0]) ^ (a >> e[1]) ^ (a >> e[2])) & 1 == be
               for e, be in zip(eqs, b)):
            return False
    return True


def legit_tuples(eqs, k):
    """DKKMS 'legitimate' k-sets of equations: pairwise disjoint, and no
    equation contains two variables from different members."""
    out = []
    for U in itertools.combinations(range(len(eqs)), k):
        vs = [set(eqs[i]) for i in U]
        if any(vs[i] & vs[j] for i in range(k) for j in range(i + 1, k)):
            continue
        owner = {}
        for t, s in enumerate(vs):
            for x in s:
                owner[x] = t
        bad = False
        for f in eqs:
            ts = {owner[x] for x in f if x in owner}
            if len(ts) >= 2:
                bad = True
                break
        if not bad:
            out.append(U)
    return out


class Block:
    """Data of one legitimate U: X_U, H_U and h_U."""

    def __init__(self, U, eqs, b):
        self.U = U
        self.vars = sorted(x for i in U for x in eqs[i])
        self.xe = [vec(eqs[i]) for i in U]
        self.H = span(self.xe)
        self.h = {}
        for bits in itertools.product((0, 1), repeat=len(U)):
            d, val = 0, 0
            for t, bit in enumerate(bits):
                if bit:
                    d ^= self.xe[t]
                    val ^= b[U[t]]
            self.h[d] = val
        self.mask = vec(self.vars)

    def subspaces(self, d):
        """All d-dimensional L <= X_U with L meet H_U = 0."""
        nz = [vec(c) for r in range(1, len(self.vars) + 1)
              for c in itertools.combinations(self.vars, r)]
        seen = set()
        for c in itertools.combinations(nz, d):
            sp = span(c)
            if dim_of(sp) == d and sp not in seen and len(sp & self.H) == 1:
                seen.add(sp)
        return sorted(seen, key=lambda s: sorted(s))


class UF:
    def __init__(self):
        self.p = {}

    def find(self, x):
        self.p.setdefault(x, x)
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, x, y):
        rx, ry = self.find(x), self.find(y)
        if rx != ry:
            self.p[rx] = ry


def folding_classes(blocks, subs):
    """Union-find closure of DKKMS folding: (U,L) ~ (U',L') iff
    L + H_U + H_U' = L' + H_U + H_U'.  subs[u] = list of subspaces of block u."""
    uf = UF()
    nb = len(blocks)
    for u in range(nb):
        for L in subs[u]:
            uf.find((u, L))
    for u in range(nb):
        for v in range(u, nb):
            Hs = span(blocks[u].xe + blocks[v].xe)
            bucket = {}
            for side, w in ((0, u), (1, v)):
                for L in subs[w]:
                    key = frozenset(x ^ y for x in L for y in Hs)
                    bucket.setdefault(key, ([], []))[side].append((w, L))
            for left, right in bucket.values():
                if left and right:
                    for z in left + right:
                        uf.union(z, left[0])
    classes = {}
    for z in list(uf.p):
        classes.setdefault(uf.find(z), []).append(z)
    return list(classes.values())


def plus(S, H):
    return frozenset(x ^ y for x in S for y in H)


def representatives(blocks, classes, fails, tag):
    """Check (a) Lemma 4.1 and (b) R meet (H_u + H_w) = 0; return
    cls_of[(u,L)] = class index and rep[c] = (u0, R)."""
    cls_of, rep = {}, []
    for c, mem in enumerate(classes):
        for z in mem:
            cls_of[z] = c
        found = None
        for (u0, R) in mem:
            if all(plus(L, blocks[w].H) == plus(R, blocks[w].H) for (w, L) in mem):
                found = (u0, R)
                break
        if found is None:
            fails.append("%s: class %d has no Lemma 4.1 representative" % (tag, c))
            rep.append(None)
            continue
        R = found[1]
        us = sorted({w for (w, _) in mem})
        for i in us:
            for j in us:
                if len(R & span(blocks[i].xe + blocks[j].xe)) != 1:
                    fails.append("%s: R meets H_u + H_w nontrivially" % tag)
        rep.append(found)
    return cls_of, rep


def decompose(R, blk, x):
    """x = q + d with q in R, d in H_U (unique when R meet H_U = 0)."""
    sols = [(x ^ d, d) for d in blk.H if (x ^ d) in R]
    assert len(sols) == 1, "decomposition not unique"
    return sols[0]


def functionals(R):
    """All linear functionals on R, as dicts vector -> bit."""
    basis = []
    for v in sorted(R):
        if v and v not in span(basis):
            basis.append(v)
    out = []
    for vals in itertools.product((0, 1), repeat=len(basis)):
        f = {0: 0}
        for v, a in zip(basis, vals):
            f.update({x ^ v: f[x] ^ a for x in list(f)})
        out.append(f)
    return out


def all_subspaces(S, only=None):
    """Nonzero subspaces of the subspace S (of dimension `only` if given)."""
    nz = [v for v in S if v]
    seen = set()
    for d in ([only] if only else range(1, dim_of(S) + 1)):
        for c in itertools.combinations(nz, d):
            sp = span(c)
            if dim_of(sp) == d:
                seen.add(sp)
    return sorted(seen, key=lambda s: (len(s), sorted(s)))


def v_choices(blk, eqs):
    """All V <= U of the DKKMS edge distribution: each equation kept whole
    or reduced to one variable."""
    opts = [[vec(eqs[i])] + [1 << x for x in eqs[i]] for i in blk.U]
    return [sum(c) for c in itertools.product(*opts)]


def derivable(Vmask, blk, eqs):
    if Vmask & ~blk.mask:
        return False
    return all(bin(Vmask & vec(eqs[i])).count("1") in (1, 3) for i in blk.U)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20260917)
    ap.add_argument("--n", type=int, default=12)
    ap.add_argument("--eqs", type=int, default=8)
    ap.add_argument("--l", type=int, default=2)
    ap.add_argument("--bvertices", type=int, default=300)
    ap.add_argument("--pairs", type=int, default=6)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    k, ell = 2, args.l
    fails = []

    for _ in range(200):
        eqs, b = make_instance(rng, args.n, args.eqs)
        legit = legit_tuples(eqs, k)
        if len(eqs) == args.eqs and 6 <= len(legit) <= 16:
            break
    else:
        print("could not generate instance")
        return 2
    unsat = unsatisfiable(args.n, eqs, b)
    print("equations", eqs, "rhs", b, "legit U:", len(legit), "unsatisfiable:", unsat)
    if not unsat:
        fails.append("3LIN instance is satisfiable")
    blocks = [Block(U, eqs, b) for U in legit]

    subs, cls_of, rep = {}, {}, {}
    for d in range(1, ell + 1):
        subs[d] = [blk.subspaces(d) for blk in blocks]
        classes = folding_classes(blocks, subs[d])
        multi = sum(1 for c in classes if len({w for (w, _) in c}) > 1)
        print("dim", d, "vertices", sum(map(len, subs[d])), "classes", len(classes),
              "classes spanning several U:", multi)
        cls_of[d], rep[d] = representatives(blocks, classes, fails, "dim %d" % d)

    class_blocks = {}
    for (w, L), c in cls_of[ell].items():
        class_blocks.setdefault(c, set()).add(w)
    class_blocks = {c: sorted(s) for c, s in class_blocks.items()}
    label_cache = {}

    def label(c, M):
        key = (c, M)
        if key in label_cache:
            return label_cache[key]
        R = rep[ell][c][1]
        us = class_blocks[c]
        vals = set()
        m = dim_of(M)
        for u in us:
            blk = blocks[u]
            Q = cls_of[m].get((u, M))
            if Q is None:
                fails.append("(U, M) not a dim-m vertex")
                continue
            RQ = rep[m][Q][1]
            vals.add(tuple(blk.h[decompose(RQ, blk, r)[1]] for r in sorted(M)))
        if len(vals) != 1:
            fails.append("gauge label depends on the member U")
        f = dict(zip(sorted(M), sorted(vals)[0]))
        label_cache[key] = f
        return f

    # B-vertices (V, L') and their A-neighbours (U, L) with L' <= L.
    bverts = set()
    for blk in blocks:
        for Vm in v_choices(blk, eqs):
            XV = span([1 << x for x in range(args.n) if Vm >> x & 1])
            for Lp in all_subspaces(XV, ell - 1):
                bverts.add((Vm, Lp))
    bverts = sorted(bverts, key=lambda t: (t[0], sorted(t[1])))
    rng.shuffle(bverts)
    stats = dict(edges=0, view_pairs=0, exact=0, predicted_mismatch=0,
                 gauge_violations=0, zero_violations=0, full_view_exact=0)
    used = 0
    for Vm, Lp in bverts:
        if used >= args.bvertices:
            break
        nbrs = [(w, L) for w, blk in enumerate(blocks) if derivable(Vm, blk, eqs)
                for L in subs[ell][w] if Lp <= L]
        pairs = [(z1, z2) for z1 in nbrs for z2 in nbrs if z1 != z2]
        if not pairs:
            continue
        used += 1
        for z1, z2 in rng.sample(pairs, min(args.pairs, len(pairs))):
            stats["edges"] += 1
            check_edge(z1, z2, Lp, blocks, cls_of[ell], rep[ell], label, stats)
    print("stats", stats)
    fails.extend(["exactness characterisation mismatch"] * min(stats["predicted_mismatch"], 1))
    fails.extend(["gauge labelling violates an exact triple"] * min(stats["gauge_violations"], 1))
    if stats["exact"] == 0 or stats["zero_violations"] == 0:
        fails.append("control degenerate: no exact triples or zero labelling never fails")
    print("failures:", len(fails))
    for f in fails[:20]:
        print("  FAIL", f)
    return 1 if fails else 0


def check_edge(z1, z2, Lp, blocks, cls_of, rep, label, stats):
    sides = []
    for (w, L) in (z1, z2):
        c = cls_of[(w, L)]
        R = rep[c][1]
        blk = blocks[w]
        dec = {x: decompose(R, blk, x) for x in Lp}
        sides.append((c, R, blk, dec))
    F = [functionals(s[1]) for s in sides]

    def unfold(side, f):
        return tuple(f[q] ^ side[2].h[d] for x in sorted(Lp) for (q, d) in [side[3][x]])

    u2 = {}
    for f2 in F[1]:
        u2.setdefault(unfold(sides[1], f2), []).append(f2)
    He = [(f1, f2) for f1 in F[0] for f2 in u2.get(unfold(sides[0], f1), [])]
    views = [all_subspaces(s[1]) for s in sides]
    for M1 in views[0]:
        for M2 in views[1]:
            stats["view_pairs"] += 1
            rel = {(tuple(f1[x] for x in sorted(M1)), tuple(f2[x] for x in sorted(M2)))
                   for f1, f2 in He}
            left = {a for a, _ in rel}
            right = {bb for _, bb in rel}
            exact = len(rel) == len(left) == len(right)
            N1 = frozenset(x for x in Lp if sides[0][3][x][0] in M1)
            N2 = frozenset(x for x in Lp if sides[1][3][x][0] in M2)
            predicted = (N1 == N2 and dim_of(N1) == dim_of(M1) == dim_of(M2))
            if exact != predicted:
                stats["predicted_mismatch"] += 1
            if not exact:
                continue
            stats["exact"] += 1
            if dim_of(M1) == dim_of(sides[0][1]):
                stats["full_view_exact"] += 1
            g1, g2 = label(sides[0][0], M1), label(sides[1][0], M2)
            for x in N1:
                q1, d1 = sides[0][3][x]
                q2, d2 = sides[1][3][x]
                if g1[q1] ^ sides[0][2].h[d1] != g2[q2] ^ sides[1][2].h[d2]:
                    stats["gauge_violations"] += 1
                    break
            for x in N1:
                q1, d1 = sides[0][3][x]
                q2, d2 = sides[1][3][x]
                if sides[0][2].h[d1] != sides[1][2].h[d2]:
                    stats["zero_violations"] += 1
                    break


if __name__ == "__main__":
    sys.exit(main())
