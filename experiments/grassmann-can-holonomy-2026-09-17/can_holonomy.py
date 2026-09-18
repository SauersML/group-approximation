#!/usr/bin/env python3
"""Folded restriction coarsening Can of a 3LIN outer game: does folding create holonomy?

Outer game: 3LIN over F_2, equation u has support vector e_u (3 variables) and RHS b_u.
A prover label for u is x_u in F_2^{vars(u)} with <e_u, x_u> = b_u (folding by the RHS).

Maximal one-bit restriction verifier (affine views, as in Grassmann/subspace encodings):
the view of u at a nonzero point s supported on vars(u), s not in {0, e_u}, is <x_u, s>.
Its kernel quotient is the one-bit label f_u(s); folding identifies f_u(s ^ e_u) = f_u(s) + b_u,
so a Can vertex is (u, {s, s ^ e_u}).  An exact cross triple between u and u' exists for each
global vector s supported on vars(u) & vars(u') (the shared "v" coordinates): the constraint is
f_u(s) = f_u'(s).  This is exactly Can(Phi, V) of the collapse theorem for this verifier.

Can is a Max-2Lin(2) system.  val(Can) = 1 iff every cycle has even parity.  The script
builds Can, finds parity conflicts by union-find, and certifies each conflict by the dependency
it realizes: the multiset of equations whose folding shifts were used sums to 0 in F_2^n with
RHS sum 1 (an odd 3LIN dependency).  YES instances (consistent RHS) must give val(Can) = 1.
"""
import itertools, random, sys


def build_can(n, eqs):
    """eqs: list of (support_mask, rhs).  Returns (#vertices, edges[(a, b, parity, used_eqs)])."""
    vid = {}
    pts = {}  # vertex id -> (u, representative s)

    def vertex(u, s):
        e = eqs[u][0]
        key = (u, min(s, s ^ e))
        if key not in vid:
            vid[key] = len(vid)
            pts[vid[key]] = key
        # parity offset of f_u(s) relative to the representative
        off = eqs[u][1] if s != key[1] else 0
        return vid[key], off, (u,) if off or s != key[1] else ()

    edges = []
    for u, w in itertools.combinations(range(len(eqs)), 2):
        common = eqs[u][0] & eqs[w][0]
        sub = common
        while sub:
            s = sub
            sub = (sub - 1) & common
            if s == eqs[u][0] or s == eqs[w][0]:
                continue
            a, oa, ua = vertex(u, s)
            b, ob, ub = vertex(w, s)
            shift_u = (u,) if s != min(s, s ^ eqs[u][0]) else ()
            shift_w = (w,) if s != min(s, s ^ eqs[w][0]) else ()
            edges.append((a, b, oa ^ ob, shift_u + shift_w))
    return len(vid), edges, pts


def holonomy(n, eqs):
    nv, edges, pts = build_can(n, eqs)
    parent = list(range(nv))
    par = [0] * nv
    uses = [frozenset()] * nv  # equations whose shifts connect v to its root (mod 2)

    def find(v):
        if parent[v] == v:
            return v, 0, frozenset()
        r, p, us = find(parent[v])
        parent[v], par[v], uses[v] = r, par[v] ^ p, uses[v] ^ us
        return r, par[v], uses[v]

    conflicts = []
    for a, b, p, used in edges:
        ra, pa, ua = find(a)
        rb, pb, ub = find(b)
        if ra != rb:
            parent[ra] = rb
            par[ra] = pa ^ pb ^ p
            uses[ra] = ua ^ ub ^ frozenset(used)
        elif pa ^ pb ^ p:
            conflicts.append(ua ^ ub ^ frozenset(used))
    return nv, len(edges), conflicts


def certify(eqs, cyc):
    tot, rhs = 0, 0
    for u in cyc:
        tot ^= eqs[u][0]
        rhs ^= eqs[u][1]
    return tot == 0 and rhs == 1


def random_instance(n, m, rng):
    eqs = []
    for _ in range(m):
        e = 0
        for i in rng.sample(range(n), 3):
            e |= 1 << i
        eqs.append([e, rng.randrange(2)])
    return eqs


def consistent(n, eqs):
    rows = [(e, b) for e, b in eqs]
    piv = []
    for e, b in rows:
        for pe, pb in piv:
            if e & (pe & -pe):
                e ^= pe; b ^= pb
        if e == 0:
            if b:
                return False
            continue
        piv = [((pe ^ e, pb ^ b) if pe & (e & -e) else (pe, pb)) for pe, pb in piv]
        piv.append((e, b))
    return True


def main():
    rng = random.Random(20260917)
    # Toy: 4-cycle of equations sharing one variable each, odd dependency.
    toy = [[0b000111, 0], [0b011100, 0], [0b110001, 0], [0b101010, 1]]
    nv, ne, conf = holonomy(6, toy)
    print(f"toy 4-cycle (shares 1 var): vertices={nv} edges={ne} conflicts={len(conf)}")
    # (Can is a perfect matching here: one-variable overlaps give no cycles, so val(Can)=1
    #  although the input is inconsistent.  Holonomy needs two-variable overlaps.)
    # Toy with two-variable overlaps: all four triples on 4 variables sum to 0 (each variable
    # three times -> not 0), so use the 6-variable K4-type system below via random search.
    for n, m in [(6, 8), (8, 12), (10, 16), (12, 24), (20, 60)]:
        yes_bad = no_hol = no_tot = cert_fail = 0
        for trial in range(300):
            eqs = random_instance(n, m, rng)
            ok = consistent(n, eqs)
            nv, ne, conf = holonomy(n, eqs)
            if ok and conf:
                yes_bad += 1
            if not ok:
                no_tot += 1
                no_hol += bool(conf)
            cert_fail += sum(not certify(eqs, c) for c in conf)
        print(f"n={n} m={m}: YES with conflict={yes_bad}  NO with holonomy={no_hol}/{no_tot}"
              f"  uncertified conflicts={cert_fail}")


if __name__ == "__main__":
    main()
