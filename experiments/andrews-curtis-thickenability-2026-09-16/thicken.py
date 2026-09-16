#!/usr/bin/env python3
"""Exact thickenability test for one-vertex presentation 2-complexes.

Words: lowercase letter = generator, uppercase = its inverse.  A relator is a
word in the free monoid on the letters (it is NOT freely reduced by this code;
the 2-complex of a non-reduced word differs from that of its reduction).

Criterion (proof in research/artifacts/andrews-curtis-thickenability-2026-09-16.md):
the presentation complex K embeds in an ORIENTABLE 3-manifold iff for every
generator g there is a cyclic order pi_g on the occurrences of g^{+-1} such that
the vertex link Lk(v) (vertices g_out, g_in; one edge per corner) with rotation
pi_g at g_out and reverse(pi_g) at g_in is a planar rotation system, i.e.
V - E + F = 2c summed over the c non-trivial components.

Half-edge ids: hid(g, s, k) with s = 0 (g_out, start of a positive letter) and
s = 1 (g_in, end of a positive letter); k indexes the occurrences of g^{+-1}.
alpha = corner involution, sigma = rotation, faces = cycles of sigma o alpha.

Variant 'orient'  : rotation at g_in is the reverse of pi_g (exact criterion).
Variant 'either'  : per generator, same or reverse (necessary condition for
                    embedding in any 3-manifold, ignoring two-sidedness).
"""
import itertools
import sys


def letters_of(rel):
    return [(ch.lower(), 1 if ch.islower() else -1) for ch in rel]


class Complex:
    def __init__(self, relators):
        self.relators = list(relators)
        self.gens = sorted({ch.lower() for r in relators for ch in r})
        occ = {g: 0 for g in self.gens}
        lets = []
        for r in relators:
            lst = []
            for g, e in letters_of(r):
                lst.append((g, e, occ[g]))
                occ[g] += 1
            lets.append(lst)
        self.occ = occ
        base, b = {}, 0
        for g in self.gens:
            base[g] = b
            b += 2 * occ[g]
        self.base = base
        self.H = b
        alpha = [-1] * b
        for lst in lets:
            L = len(lst)
            for p in range(L):
                g, e, k = lst[p]
                g2, e2, k2 = lst[(p + 1) % L]
                h1 = self.hid(g, 1 if e == 1 else 0, k)     # end of letter p
                h2 = self.hid(g2, 0 if e2 == 1 else 1, k2)  # start of letter p+1
                assert alpha[h1] == -1 and alpha[h2] == -1
                alpha[h1] = h2
                alpha[h2] = h1
        assert all(a >= 0 for a in alpha)
        self.alpha = alpha
        # components of the link graph on vertices (g, s)
        parent = {}

        def find(u):
            while parent[u] != u:
                parent[u] = parent[parent[u]]
                u = parent[u]
            return u
        verts = [(g, s) for g in self.gens for s in (0, 1)]
        for v in verts:
            parent[v] = v
        for h in range(b):
            u, w = find(self.vert(h)), find(self.vert(alpha[h]))
            if u != w:
                parent[u] = w
        self.V = len(verts)
        self.E = b // 2
        self.c = len({find(v) for v in verts})
        self.F_target = self.E - self.V + 2 * self.c

    def hid(self, g, s, k):
        return self.base[g] + s * self.occ[g] + k

    def vert(self, h):
        for g in self.gens:
            if self.base[g] <= h < self.base[g] + 2 * self.occ[g]:
                return (g, (h - self.base[g]) // self.occ[g])
        raise ValueError(h)


def faces(sigma, alpha):
    H = len(alpha)
    seen = bytearray(H)
    F = 0
    for h in range(H):
        if not seen[h]:
            F += 1
            x = h
            while not seen[x]:
                seen[x] = 1
                x = sigma[alpha[x]]
    return F


def sigma_from(K, orders, flips):
    """orders[g] = list (cyclic order of occurrences), flips[g] True = reverse at g_in."""
    sigma = [-1] * K.H
    for g in K.gens:
        pi = orders[g]
        d = len(pi)
        for i in range(d):
            a, bnext = pi[i], pi[(i + 1) % d]
            sigma[K.hid(g, 0, a)] = K.hid(g, 0, bnext)
            if flips[g]:
                sigma[K.hid(g, 1, bnext)] = K.hid(g, 1, a)
            else:
                sigma[K.hid(g, 1, a)] = K.hid(g, 1, bnext)
    return sigma


def brute(K, variant="orient"):
    """Reference implementation: enumerate all prod (d_g - 1)! (x 2^n) rotations."""
    choices = []
    for g in K.gens:
        d = K.occ[g]
        choices.append([[0] + list(p) for p in itertools.permutations(range(1, d))])
    flipsets = [dict((g, True) for g in K.gens)]
    if variant == "either":
        flipsets = [dict(zip(K.gens, fl)) for fl in itertools.product([True, False], repeat=len(K.gens))]
    n = 0
    for fl in flipsets:
        for combo in itertools.product(*choices):
            n += 1
            orders = dict(zip(K.gens, combo))
            if faces(sigma_from(K, orders, fl), K.alpha) == K.F_target:
                return True, (orders, fl), n
    return False, None, n


def dfs(K, variant="orient", want_witness=True):
    """Exact branch-and-bound search over the same rotation space as brute().

    Adding sigma[a] = b adds the arc alpha[a] -> b to the functional graph of
    phi = sigma o alpha.  Starting from H singleton paths, every arc either
    merges two paths or closes one path into a cycle, so after all H arcs
    F = H - merges.  merges never decreases, so a branch with
    merges > H - F_target can never reach F = F_target and is pruned.  The
    pruning is therefore complete: dfs() and brute() agree (checked in tests).
    """
    H, alpha = K.H, K.alpha
    limit = H - K.F_target
    pstart = list(range(H))
    pend = list(range(H))
    state = {"merges": 0, "nodes": 0}
    stack = []

    def add(u, w):  # arc u -> w
        s, e = pstart[u], pend[w]
        if s == w:
            stack.append(None)
        else:
            stack.append((s, pend[s], e, pstart[e]))
            pend[s] = e
            pstart[e] = s
            state["merges"] += 1

    def undo():
        rec = stack.pop()
        if rec is not None:
            s, ps, e, pe = rec
            pend[s] = ps
            pstart[e] = pe
            state["merges"] -= 1

    gens = sorted(K.gens, key=lambda g: K.occ[g])
    orders = {}
    flips = {}
    result = []

    def link(g, a, b, flip):
        # sigma_out(a) = b ; at g_in the reverse (flip) or the same order
        add(alpha[K.hid(g, 0, a)], K.hid(g, 0, b))
        if flip:
            add(alpha[K.hid(g, 1, b)], K.hid(g, 1, a))
        else:
            add(alpha[K.hid(g, 1, a)], K.hid(g, 1, b))

    def gen_step(gi):
        if gi == len(gens):
            assert H - state["merges"] <= K.F_target
            if state["merges"] == limit:
                result.append((dict((g, list(v)) for g, v in orders.items()), dict(flips)))
                return True
            return False
        g = gens[gi]
        d = K.occ[g]
        flipchoices = [True] if (variant == "orient" or d <= 2) else [True, False]
        for fl in flipchoices:
            flips[g] = fl
            pi = [0]
            orders[g] = pi
            used = [False] * d
            used[0] = True
            if extend(gi, g, d, fl, pi, used):
                return True
        return False

    def extend(gi, g, d, fl, pi, used):
        state["nodes"] += 1
        last = pi[-1]
        if len(pi) == d:
            link(g, last, 0, fl)
            ok = False
            if state["merges"] <= limit:
                ok = gen_step(gi + 1)
            undo(); undo()
            return ok
        for k in range(1, d):
            if used[k]:
                continue
            link(g, last, k, fl)
            if state["merges"] <= limit:
                used[k] = True
                pi.append(k)
                ok = extend(gi, g, d, fl, pi, used)
                pi.pop()
                used[k] = False
                if ok:
                    undo(); undo()
                    return True
            undo(); undo()
        return False

    found = gen_step(0)
    return found, (result[0] if result else None), state["nodes"]


def thickenable(relators, variant="orient"):
    K = Complex(relators)
    ok, wit, nodes = dfs(K, variant)
    return ok, wit, nodes, K
