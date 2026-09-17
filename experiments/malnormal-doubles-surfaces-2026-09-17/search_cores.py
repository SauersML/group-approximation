"""Complete enumeration of cyclic cores along a fixed word w in C.

Let w be a cyclically reduced, non-proper-power closed path at a vertex c of
Gamma_C.  If A <= F_2 is finitely generated, A cap C^g = <w> (g the path to c),
and w is filling in A (not in a proper free factor), then w crosses every edge
of Gamma_A (at least twice), so Gamma_A is the folded quotient of the circle
graph of w obtained by identifying some of its n vertices.  Such a quotient is
determined by the partition of Z/n it induces.

This script walks the lattice of these partitions from the discrete one,
identifying one pair at a time and folding.  A partition is kept only if the
component of (base, c) in Gamma_A x Gamma_C still has rank 1.  If A' <= A then
A' cap C^g <= A cap C^g, so pruning loses nothing: every partition with rank-1
component is reached through a chain of partitions with rank-1 component.
The enumeration is therefore COMPLETE for the given w: it lists every Gamma_A
with A cap C^g = <w> in which w crosses every edge.

Output for each w: number of admissible partitions, maximum rank of Gamma_A
among them, and a certificate (rank >= 2 and Stallings' filling criterion
after greedy Whitehead reduction) if one exists.  "maxrank 1" is an exact
negative: no cyclic core of rank >= 2 exists along this w.

Usage: python3 search_cores.py <maxlen> <node_cap> <C words ...>
"""
import sys
from stallings import INV, word, show, fold_subgroup, read, product_component_rank, rank, is_malnormal, offdiag_depth
from search_filling import graph_basis_word, minimize, whitehead_filling
from search_quotients import closed_paths, primitive_root_free, inv


def partition(A, w):
    lab, out, v = {}, [], 0
    for i in range(len(w)):
        out.append(lab.setdefault(v, len(lab)))
        v = A.adj[v][w[i]]
    return tuple(out)


def cores(C, c, w, node_cap):
    n = len(w)
    start = fold_subgroup([w])
    seen = {partition(start, w)}
    stack = [[w]]
    maxrank, cert, nodes = 1, None, 0
    while stack:
        gens = stack.pop()
        A = fold_subgroup(gens)
        nodes += 1
        if nodes > node_cap:
            return nodes, maxrank, cert, False
        rA = rank(A)
        if rA >= 2:
            maxrank = max(maxrank, rA)
            if cert is None:
                bw, k = graph_basis_word(A, 0, w)
                if whitehead_filling(minimize(bw, k), k):
                    cert = [show(g) for g in gens]
        p = partition(A, w)
        for i in range(n):
            for j in range(i + 1, n):
                if p[i] == p[j]:
                    continue
                g = gens + [w[:i] + inv(w[:j])]
                B = fold_subgroup(g)
                q = partition(B, w)
                if q in seen:
                    continue
                seen.add(q)
                r, _ = product_component_rank(B, 0, C, c)
                if r == 1:
                    stack.append(g)
    return nodes, maxrank, cert, True


def run(Cwords, N, node_cap):
    C = fold_subgroup([word(g) for g in Cwords])
    print("C", Cwords, "V", C.nv(), "rank", rank(C), "malnormal", is_malnormal(C),
          "K", offdiag_depth(C) if is_malnormal(C) else None)
    done = set()
    certs = 0
    for L in range(2, N + 1):
        count = complete = 0
        for c in range(C.nv()):
            for w in closed_paths(C, c, L):
                if len(w) != L or not primitive_root_free(w):
                    continue
                canon = min(min(tuple(u[i:] + u[:i]) for i in range(L)) for u in (w, inv(w)))
                if canon in done:
                    continue
                done.add(canon)
                nodes, mr, cert, full = cores(C, c, w, node_cap)
                count += 1
                complete += full
                if mr >= 2 or cert or not full:
                    print("  w", show(w), "c", c, "partitions", nodes, "maxrank", mr,
                          "complete", full, "CERT" if cert else "", cert or "")
                if cert:
                    certs += 1
        print(" |w| =", L, ": cyclic words", count, "complete", complete, "certificates so far", certs)
        sys.stdout.flush()


if __name__ == "__main__":
    run(sys.argv[3:], int(sys.argv[1]), int(sys.argv[2]))
