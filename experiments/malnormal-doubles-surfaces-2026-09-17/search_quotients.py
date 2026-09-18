"""Quotient search for filling cyclic cores in D(F_2, C).

Start from w in C (a cyclically reduced closed path at a vertex c of Gamma_C) and
the circle graph of w (A = <w>, A cap C = <w>).  Identify two vertices of the
current graph (i.e. add the generator w[:i] w[:j]^-1) and fold.  The intersection
A cap C only grows under this, so a branch dies as soon as the fibre-product
component of (base, c) has rank >= 2.  A leaf is a certificate when w is filling
in A (search_filling.whitehead_filling after Whitehead reduction).

Usage: python3 search_quotients.py <maxlen> <depth> <C words ...>
"""
import sys
from stallings import INV, word, show, fold_subgroup, read, product_component_rank, rank, is_malnormal, offdiag_depth, infinite_index
from search_filling import graph_basis_word, minimize, whitehead_filling


def closed_paths(C, c, N):
    """Cyclically reduced closed paths at c of length <= N (as words)."""
    out = []
    stack = [(c, [])]
    while stack:
        u, w = stack.pop()
        if w and u == c and w[0] != INV(w[-1]):
            out.append(w)
        if len(w) == N:
            continue
        for x, u2 in C.adj[u].items():
            if w and x == INV(w[-1]):
                continue
            stack.append((u2, w + [x]))
    return out


def primitive_root_free(w):
    n = len(w)
    return all(not (n % d == 0 and w == w[:d] * (n // d)) for d in range(1, n))


def inv(w):
    return [INV(x) for x in reversed(w)]


def certificate(C, c, w, depth):
    n = len(w)
    best = [None]
    seen = set()

    def rec(gens, d, start):
        A = fold_subgroup(gens)
        key = (A.nv(), tuple(sorted(tuple(sorted(dd.items())) for dd in A.adj)))
        if key in seen:
            return None
        seen.add(key)
        r, _ = product_component_rank(A, 0, C, c)
        if r != 1:
            return None
        if rank(A) >= 2:
            bw, k = graph_basis_word(A, 0, w)
            if whitehead_filling(minimize(bw, k), k):
                return [show(g) for g in gens]
        if d == 0:
            return None
        for i in range(start, n):
            for j in range(i + 1, n):
                g = w[:i] + inv(w[:j])
                res = rec(gens + [g], d - 1, i)
                if res:
                    return res
        return None

    return rec([w], depth, 0)


def run(Cwords, N, depth):
    C = fold_subgroup([word(g) for g in Cwords])
    print("C", Cwords, "V", C.nv(), "rank", rank(C), "malnormal", is_malnormal(C),
          "K", offdiag_depth(C) if is_malnormal(C) else None)
    done = set()
    for L in range(2, N + 1):
        for c in range(C.nv()):
            for w in closed_paths(C, c, L):
                if len(w) != L or not primitive_root_free(w):
                    continue
                canon = min(tuple(w[i:] + w[:i]) for i in range(L))
                if canon in done:
                    continue
                done.add(canon)
                cert = certificate(C, c, w, depth)
                if cert:
                    print("CERT c", c, "w", show(w), "A gens", cert)
                    return cert
        print(" no certificate with |w| <=", L)
        sys.stdout.flush()
    return None


if __name__ == "__main__":
    run(sys.argv[3:], int(sys.argv[1]), int(sys.argv[2]))
