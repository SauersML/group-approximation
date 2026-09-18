"""Certificate search for closed surface subgroups in doubles D(F_2, C).

Criterion (see research/malnormal-free-doubles-surface-certificates-proof.md):
if Y is a folded genus-1 fatgraph over F_2 with one boundary word w, and for
some vertex c of the Stallings graph Gamma_C the word w reads a closed path at c
and the component of (p, c) in the fibre product Y x Gamma_C has rank 1, then
pi_1(Y) *_<w> pi_1(Y)-bar is a closed genus-2 surface group inside D(F_2, C).

Two genus-1 one-boundary fatgraph shapes exist:
  rose  (one 4-valent vertex, petals x, y):   w = x y X Y
  theta (two trivalent vertices, edges x,y,z): w = x Y z X y Z
If C is malnormal, every edge word of a certificate has length <= K(C), the
longest reduced path in the off-diagonal part of Gamma_C x Gamma_C, so the
search with L = K(C) is exhaustive for genus 1.

Usage: python3 search_genus1.py            (calibrations + batch)
"""
import random
import sys
from stallings import (INV, Graph, word, show, reduce_word, fold_subgroup, read,
                       product_component_rank, is_malnormal, offdiag_depth,
                       infinite_index, rank, check_folded)


def inv(w):
    return [INV(x) for x in reversed(w)]


def paths_from(C, v, L):
    """All nonempty reduced words of length <= L readable from v, with endpoints."""
    out = []
    stack = [(v, [], None)]
    while stack:
        u, w, last = stack.pop()
        if w:
            out.append((w, u))
        if len(w) == L:
            continue
        for x, u2 in C.adj[u].items():
            if last is not None and x == INV(last):
                continue
            stack.append((u2, w + [x], x))
    return out


def build_graph(n_vertices, edges):
    """Subdivided graph from (v, word, u) edges; returns Graph or None if not folded."""
    G = Graph()
    for _ in range(n_vertices):
        G.new()
    for v, w, u in edges:
        cur = v
        for i, x in enumerate(w):
            nxt = u if i == len(w) - 1 else G.new()
            if x in G.adj[cur] or INV(x) in G.adj[nxt]:
                return None
            G.adj[cur][x] = nxt
            G.adj[nxt][INV(x)] = cur
            cur = nxt
    return G


def rose(x, y):
    return build_graph(1, [(0, x, 0), (0, y, 0)])


def theta(x, y, z):
    return build_graph(2, [(0, x, 1), (0, y, 1), (0, z, 1)])


def certify(C, Y, w, c):
    """Return True if (Y, w, c) is a certificate for D(F_2, C)."""
    if read(C, c, w) != c:
        return False
    r, _ = product_component_rank(Y, 0, C, c)
    return r == 1


def search(C, L, first_only=True):
    certs = []
    for c in range(C.nv()):
        for x, c1 in paths_from(C, c, L):
            # rose: x y X Y
            for y, c2 in paths_from(C, c1, L):
                c3 = read(C, c2, inv(x))
                if c3 is not None and read(C, c3, inv(y)) == c:
                    Y = rose(x, y)
                    if Y is not None:
                        w = x + y + inv(x) + inv(y)
                        if certify(C, Y, w, c):
                            certs.append(("rose", show(x), show(y), c))
                            if first_only:
                                return certs
            # theta: x Y z X y Z ; Y-path read from c1 means reading inv(y)
            for yi, c2 in paths_from(C, c1, L):
                y = inv(yi)
                for z, c3 in paths_from(C, c2, L):
                    c4 = read(C, c3, inv(x))
                    if c4 is None:
                        continue
                    c5 = read(C, c4, y)
                    if c5 is None or read(C, c5, inv(z)) != c:
                        continue
                    Y = theta(x, y, z)
                    if Y is None:
                        continue
                    w = x + inv(y) + z + inv(x) + y + inv(z)
                    if certify(C, Y, w, c):
                        certs.append(("theta", show(x), show(y), show(z), c))
                        if first_only:
                            return certs
    return certs


def describe(gens):
    C = fold_subgroup([word(g) for g in gens])
    assert check_folded(C)
    mal = is_malnormal(C)
    K = offdiag_depth(C) if mal else None
    return C, mal, K


def calibrate():
    print("== calibration ==")
    # C = F_2: finite index, fibre product is Y itself (rank 2): never certifies.
    C = fold_subgroup([word("a"), word("b")])
    print("C=F_2: certs with L=2:", len(search(C, 2, first_only=False)))
    # C = <[a,b]>: known (Kim-Oum / Wilton) genus-2 surface; must certify.
    C, mal, K = describe(["abAB"])
    print("C=<abAB>: malnormal", mal, "K", K, "cert", search(C, max(K, 1)))
    # C = <aa, bb>: not malnormal (double not hyperbolic); criterion still valid.
    C, mal, K = describe(["aa", "bb"])
    print("C=<aa,bb>: malnormal", mal, "cert", search(C, 3))


def random_word(L, rng):
    w = []
    while len(w) < L:
        x = rng.randrange(4)
        if w and w[-1] == INV(x):
            continue
        w.append(x)
    return w


def batch(n, lo, hi, seed):
    rng = random.Random(seed)
    tried = certified = 0
    fails = []
    seen = set()
    while tried < n:
        g1 = random_word(rng.randint(lo, hi), rng)
        g2 = random_word(rng.randint(lo, hi), rng)
        C = fold_subgroup([g1, g2])
        if rank(C) != 2 or not infinite_index(C) or not is_malnormal(C):
            continue
        key = (show(g1), show(g2))
        if key in seen:
            continue
        seen.add(key)
        tried += 1
        K = offdiag_depth(C)
        certs = search(C, K)
        if certs:
            certified += 1
            print("CERT", key, "V", C.nv(), "K", K, certs[0])
        else:
            fails.append((key, C.nv(), K))
            print("NONE", key, "V", C.nv(), "K", K)
        sys.stdout.flush()
    print("batch", lo, hi, "seed", seed, ":", certified, "/", tried, "certified")
    return fails


if __name__ == "__main__":
    calibrate()
    args = sys.argv[1:]
    n = int(args[0]) if args else 20
    lo = int(args[1]) if len(args) > 1 else 4
    hi = int(args[2]) if len(args) > 2 else 8
    batch(n, lo, hi, 20260917)
