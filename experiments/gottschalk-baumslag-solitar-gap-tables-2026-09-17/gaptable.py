#!/usr/bin/env python3
"""Directed search for gap tables inside BS(p,q).

For memory sets S, M in the ball of radius R of G = BS(p,q) (both containing 1, |S| = ns, |M| = nm):

  T   = forward table T_f(S, M)  (cells (s, m) grouped by the element s m of G);
  gap = two reverse cells (m, s), (m', s') with m s != m' s' in G but equal in H = Z[1/pq] x| Z,
        i.e. merged in every finite quotient of G;
  cert = Tietze elimination of the table group P(T) down to two letters u, v whose values are a^+-1, t^+-1,
        with some remaining relator equal (after substitution, up to cyclic permutation and inversion) to the
        BS relator and every remaining relator trivial in G. Then P(T) -> G, x_a -> a, is an isomorphism.

With cert, the reverse pair is distinct in P(T) and merged in every finite quotient of P(T): T is a gap table.

Library: tietze elimination and the certificate.
"""
import itertools
import json
import sys
import time

from bsgroup import BS, ball, free_reduce, inv, wstr


def cyc_reduce(w):
    w = free_reduce(w)
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return w


def cyclic_perms(w):
    return {tuple(w[i:] + w[:i]) for i in range(len(w))}


def tietze(ngen, relators):
    defs = {g: [g] for g in range(1, ngen + 1)}
    rels = [cyc_reduce(r) for r in relators]
    rels = [r for r in rels if r]
    alive = set(range(1, ngen + 1))
    changed = True
    while changed:
        changed = False
        # prefer shortest relator with a letter occurring once
        for r in sorted(rels, key=len):
            counts = {}
            for x in r:
                counts[abs(x)] = counts.get(abs(x), 0) + 1
            cand = [g for g, c in counts.items() if c == 1]
            if not cand:
                continue
            g = cand[0]
            i = [k for k, x in enumerate(r) if abs(x) == g][0]
            rot = r[i:] + r[:i]
            e, rest = rot[0], rot[1:]
            val = inv(rest) if e > 0 else rest

            def sub(w):
                out = []
                for x in w:
                    if x == g:
                        out += val
                    elif x == -g:
                        out += inv(val)
                    else:
                        out.append(x)
                return free_reduce(out)
            for h in defs:
                defs[h] = sub(defs[h])
            rels = [cyc_reduce(sub(q)) for q in rels if q is not r]
            rels = [q for q in rels if q]
            alive.discard(g)
            changed = True
            break
    return defs, sorted(alive), rels



def certify(G, Sw, Mw):
    """Sw, Mw: lists of words, first entry the empty word. Returns a record if (S, M) is a certified gap table."""
    p, q = G.p, G.q
    ns, nm = len(Sw), len(Mw)
    Sk = [G.nf(w) for w in Sw]; Mk = [G.nf(w) for w in Mw]
    if len(set(Sk)) != ns or len(set(Mk)) != nm or Sk[0] != (0,) or Mk[0] != (0,):
        return None
    cells = [(mi, si) for mi in range(nm) for si in range(ns)]
    rk = {c: G.nf(Mw[c[0]] + Sw[c[1]]) for c in cells}
    rh = {c: G.rfq(Mw[c[0]] + Sw[c[1]]) for c in cells}
    gaps = [(c, d) for c, d in itertools.combinations(cells, 2) if rh[c] == rh[d] and rk[c] != rk[d]]
    if not gaps:
        return None
    return certify_group(G, Sw, Mw, gaps)


def certify_group(G, Sw, Mw, gaps):
    p, q = G.p, G.q
    ns, nm = len(Sw), len(Mw)
    cls = {}
    for si in range(ns):
        for mi in range(nm):
            cls.setdefault(G.nf(Sw[si] + Mw[mi]), []).append((si, mi))
    classes = list(cls.values())

    def fw(si, mi):
        return ([si] if si else []) + ([ns - 1 + mi] if mi else [])
    relators = []
    for c in classes:
        for cc in c[1:]:
            relators.append(fw(*c[0]) + inv(fw(*cc)))
    val = {si: Sw[si] for si in range(1, ns)}
    for mi in range(1, nm):
        val[ns - 1 + mi] = Mw[mi]
    defs, alive, rels = tietze(ns + nm - 2, relators)
    if len(alive) != 2:
        return None
    gens = {G.nf([1]): [1], G.nf([-1]): [-1], G.nf([2]): [2], G.nf([-2]): [-2]}
    sub = {}
    for g in alive:
        k = G.nf(val[g])
        if k not in gens:
            return None
        sub[g] = gens[k]
    if {abs(sub[g][0]) for g in alive} != {1, 2}:
        return None

    def subw(w):
        o = []
        for x in w:
            o += sub[x] if x > 0 else inv(sub[-x])
        return cyc_reduce(o)
    imgs = [subw(r) for r in rels]
    for w in imgs:
        if not G.is_trivial(w):
            raise RuntimeError('bug: relator not trivial in G')
    rel = [2] + [1] * p + [-2] + [-1] * q
    targets = cyclic_perms(rel) | cyclic_perms(inv(rel))
    if not any(tuple(w) in targets for w in imgs):
        return None
    return {
        'group': 'BS(%d,%d)' % (p, q),
        'S': [wstr(w) for w in Sw],
        'M': [wstr(w) for w in Mw],
        'forward_classes': [c for c in classes if len(c) > 1],
        'relators': [[wstr(Sw[c[0][0]]) + '*' + wstr(Mw[c[0][1]]), wstr(Sw[cc[0]]) + '*' + wstr(Mw[cc[1]])]
                     for c in classes for cc in c[1:]],
        'tietze_generators': {str(g): wstr(val[g]) for g in alive},
        'remaining_relators': [wstr(w) for w in imgs],
        'gap_pairs': [[wstr(Mw[c[0]]) + '*' + wstr(Sw[c[1]]), wstr(Mw[d[0]]) + '*' + wstr(Sw[d[1]])] for c, d in gaps],
    }


def certify_iso(G, Sw, Mw, gaps):
    """General certificate that x_c -> c is an isomorphism P(T) -> G.

    Needs labels with values a^+-1 and t^+-1 (letters la, lt). After Tietze elimination the letters la, lt have
    definitions A, B (words in the alive letters). Put psi(a) = A, psi(t) = B. Accept when
      (i)  psi(t a^p t^-1 a^-q) is freely conjugate to some remaining relator or its inverse (psi is a homomorphism
           G -> P(T));
      (ii) for every alive letter g, psi(word of the label of g) freely reduces to g (psi phi = id on P(T)).
    phi psi = id on a, t holds because A, B are Tietze definitions, whose values are a^+-1, t^+-1 (sign fixed below).
    """
    p, q = G.p, G.q
    ns, nm = len(Sw), len(Mw)
    cls = {}
    for si in range(ns):
        for mi in range(nm):
            cls.setdefault(G.nf(Sw[si] + Mw[mi]), []).append((si, mi))
    classes = list(cls.values())

    def fw(si, mi):
        return ([si] if si else []) + ([ns - 1 + mi] if mi else [])
    relators = [fw(*c[0]) + inv(fw(*cc)) for c in classes for cc in c[1:]]
    val = {si: Sw[si] for si in range(1, ns)}
    for mi in range(1, nm):
        val[ns - 1 + mi] = Mw[mi]
    defs, alive, rels = tietze(ns + nm - 2, relators)
    if len(alive) != 2 or not rels:
        return None
    psi = {}
    for g, w in val.items():
        k = G.nf(w)
        for x in (1, -1, 2, -2):
            if k == G.nf([x]) and abs(x) not in psi:
                psi[abs(x)] = defs[g] if x > 0 else inv(defs[g])
    if set(psi) != {1, 2}:
        return None

    def ps(w):
        o = []
        for x in w:
            o += psi[x] if x > 0 else inv(psi[-x])
        return cyc_reduce(o)
    rel = ps([2] + [1] * p + [-2] + [-1] * q)
    ok = any(tuple(rel) in (cyclic_perms(cyc_reduce(r)) | cyclic_perms(cyc_reduce(inv(r)))) for r in rels)
    if not ok:
        return None
    for g in alive:
        if free_reduce([y for x in val[g] for y in (psi[x] if x > 0 else inv(psi[-x]))]) != [g]:
            return None
    return {
        'group': 'BS(%d,%d)' % (p, q),
        'S': [wstr(w) for w in Sw],
        'M': [wstr(w) for w in Mw],
        'forward_classes': [c for c in classes if len(c) > 1],
        'relators': [[wstr(Sw[c[0][0]]) + '*' + wstr(Mw[c[0][1]]), wstr(Sw[cc[0]]) + '*' + wstr(Mw[cc[1]])]
                     for c in classes for cc in c[1:]],
        'tietze_generators': {str(g): wstr(val[g]) for g in alive},
        'remaining_relators': [''.join('xyXY'[{1: 0, 2: 1, -1: 2, -2: 3}[1 if x == alive[0] else 2 if x == alive[1]
                                                                          else -1 if x == -alive[0] else -2]]
                                       for x in r) for r in rels],
        'gap_pairs': [[wstr(Mw[c[0]]) + '*' + wstr(Sw[c[1]]), wstr(Mw[d[0]]) + '*' + wstr(Sw[d[1]])] for c, d in gaps],
    }


def certify2(G, Sw, Mw):
    ns, nm = len(Sw), len(Mw)
    Sk = [G.nf(w) for w in Sw]; Mk = [G.nf(w) for w in Mw]
    if len(set(Sk)) != ns or len(set(Mk)) != nm or Sk[0] != (0,) or Mk[0] != (0,):
        return None
    cells = [(mi, si) for mi in range(nm) for si in range(ns)]
    rk = {c: G.nf(Mw[c[0]] + Sw[c[1]]) for c in cells}
    rh = {c: G.rfq(Mw[c[0]] + Sw[c[1]]) for c in cells}
    gaps = [(c, d) for c, d in itertools.combinations(cells, 2) if rh[c] == rh[d] and rk[c] != rk[d]]
    if not gaps:
        return None
    return certify_iso(G, Sw, Mw, gaps)
