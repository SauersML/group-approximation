#!/usr/bin/env python3
"""Canonical hosts of minimal-window incidence patterns, with Tietze reduction and torsion classification.

For a configuration (E, F) in a group G, the canonical host H has one letter per element of E and of F,
a relator f e (f' e')^-1 for each coincidence f e = f' e' in G, and a relator f e for each product equal to 1.
The letter map pi : H -> G is a homomorphism, and it is injective on FE u {1} and on F (images are distinct).

Transfer (see the artifact): LP_H(E_H, F_H) <= LP_G(E, F). So a fake in G whose host H is torsion-free
refutes torsion-free-windows-have-minimal-shannon-certificates.

Classification after Tietze elimination (every elimination is a genuine Tietze move, so H is unchanged):
  FREE           no relator left: H is free, hence torsion-free.
  ONE-REL-TF     one relator, not a proper power: torsion-free (Karrass-Magnus-Solitar).
  ONE-REL-TOR    one relator u^k, k >= 2: u has order exactly k (Karrass-Magnus-Solitar).
  TORSION        some relator is u^k with k >= 2 and pi(u) != 1: u is a nontrivial element with u^k = 1.
  UNKNOWN        none of the above.
"""
import sys


def free_reduce(w):
    out = []
    for g, s in w:
        if out and out[-1][0] == g and out[-1][1] == -s:
            out.pop()
        else:
            out.append((g, s))
    return out


def cyc_reduce(w):
    w = free_reduce(w)
    while len(w) >= 2 and w[0][0] == w[-1][0] and w[0][1] == -w[-1][1]:
        w = w[1:-1]
    return w


def inv(w):
    return [(g, -s) for g, s in reversed(w)]


def power_root(w):
    """w cyclically reduced; return (u, k) with w = u^k and k maximal."""
    n = len(w)
    for p in range(1, n + 1):
        if n % p == 0 and w == w[:p] * (n // p):
            return w[:p], n // p
    return w, 1


def canonical_host(G, E, F):
    E = list(dict.fromkeys(E)); F = list(dict.fromkeys(F))
    names = ['e%s' % G.show(e) for e in E] + ['f%s' % G.show(f) for f in F]
    image = list(E) + list(F)
    byval = {}
    for j, f in enumerate(F):
        for i, e in enumerate(E):
            byval.setdefault(G.mul(f, e), []).append((len(E) + j, i))
    rels = []
    for v, pairs in byval.items():
        f0, e0 = pairs[0]
        for f1, e1 in pairs[1:]:
            rels.append([(f0, 1), (e0, 1), (e1, -1), (f1, -1)])
        if v == G.one:
            rels.append([(f0, 1), (e0, 1)])
    return names, image, [cyc_reduce(r) for r in rels]


def substitute(w, g, repl):
    out = []
    for h, s in w:
        if h == g:
            out.extend(repl if s == 1 else inv(repl))
        else:
            out.append((h, s))
    return cyc_reduce(out)


def tietze(ngen, rels, rng=None, history=None):
    rels = [r for r in (cyc_reduce(r) for r in rels) if r]
    alive = set(range(ngen))
    changed = True
    while changed:
        changed = False
        rels.sort(key=len)
        if rng is not None:
            rng.shuffle(rels)
        for idx, r in enumerate(rels):
            for pos, (g, s) in enumerate(r):
                if sum(1 for h, _ in r if h == g) == 1:
                    A, B = r[:pos], r[pos + 1:]
                    # A g^s B = 1  =>  g^s = A^-1 B^-1
                    rhs = free_reduce(inv(A) + inv(B))
                    repl = rhs if s == 1 else inv(rhs)
                    rels = [substitute(q, g, repl) for k, q in enumerate(rels) if k != idx]
                    rels = [q for q in rels if q]
                    alive.discard(g)
                    if history is not None:
                        history.append((g, repl))
                    changed = True
                    break
            if changed:
                break
    # deduplicate up to cyclic permutation and inversion
    seen, uniq = set(), []
    for r in rels:
        keys = []
        for w in (r, inv(r)):
            for i in range(len(w)):
                keys.append(tuple(w[i:] + w[:i]))
        key = min(keys)
        if key not in seen:
            seen.add(key); uniq.append(r)
    return sorted(alive), uniq


def evaluate(G, image, w):
    x = G.one
    for g, s in w:
        x = G.mul(x, image[g] if s == 1 else G.inv(image[g]))
    return x


def classify(G, E, F, rng=None):
    names, image, rels = canonical_host(G, E, F)
    if rng is not None:
        rng.shuffle(rels)
    alive, red = tietze(len(names), rels, rng)
    if not red:
        return 'FREE', names, alive, red, None
    if len(red) == 1:
        u, k = power_root(red[0])
        if k >= 2:
            return 'ONE-REL-TOR', names, alive, red, (u, k)
        return 'ONE-REL-TF', names, alive, red, None
    for r in red:
        u, k = power_root(r)
        if k >= 2 and evaluate(G, image, u) != G.one:
            return 'TORSION', names, alive, red, (u, k)
    return 'UNKNOWN', names, alive, red, None


def word_str(names, w):
    return '.'.join(names[g] + ('' if s == 1 else '^-1') for g, s in w) or '1'


if __name__ == '__main__':
    sys.path.insert(0, '../shannon-window-certificates-2026-09-17')
    from random_scan import Cyc
    G = Cyc(3)
    kind, names, alive, red, cert = classify(G, [0, 1, 2], [0, 1])
    print(kind, [names[g] for g in alive], [word_str(names, r) for r in red], cert and (word_str(names, cert[0]), cert[1]))
