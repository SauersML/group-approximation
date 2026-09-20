"""Independent re-check of a certificate cert_*.json written by climb3.py.

Uses the exact-rational implementation salvetti_morse.py (poset order from the
Salvetti rule <D,G> <= <C',F> iff G refines F and D = G o C', computed from scratch,
not the face lists of fast_morse.py).  For each chamber C it
  1. recomputes Asc(C) (and checks that every cell has a unique lowest vertex),
  2. computes reduced Betti numbers of the order complex over F_p for two primes,
  3. checks pi_1 of the order complex is trivial by an edge-path presentation that is
     simplified to the empty presentation (a rigorous sufficient test),
  4. for m <= 2 this certifies Asc(C) is (m-1)-connected.
The heights: f_{C'}(D) = sum_{ij sep C',D} K a_ij + eta(D)  (integers)."""
import sys, json, itertools
from fractions import Fraction
from salvetti_morse import Morse, faces_below, star, leq, sepval, order_complex_homology

def pi1_trivial(els):
    """edge-path group of the order complex of the poset els; True if the presentation
    simplifies to the trivial group (sufficient for simple connectivity)."""
    N = len(els)
    if N == 0:
        return False
    lt = {(i, j) for i in range(N) for j in range(N) if i != j and leq(els[i], els[j])}
    edges = sorted(lt)
    adj = {i: [] for i in range(N)}
    for (i, j) in edges:
        adj[i].append(j); adj[j].append(i)
    # connectivity + spanning tree (BFS)
    seen = {0: None}; order = [0]
    for v in order:
        for w in adj[v]:
            if w not in seen:
                seen[w] = v; order.append(w)
    if len(seen) != N:
        return False
    tree = {(min(v, p), max(v, p)) for v, p in seen.items() if p is not None}
    gen = {}
    for (i, j) in edges:
        e = (min(i, j), max(i, j))
        if e not in tree and e not in gen:
            gen[e] = len(gen)
    def g(i, j):  # oriented edge i -> j as a word
        e = (min(i, j), max(i, j))
        if e in tree:
            return []
        return [gen[e] + 1] if i < j else [-(gen[e] + 1)]
    rels = []
    for (i, j) in edges:
        for k in range(N):
            if (j, k) in lt:  # triangle i < j < k
                w = g(i, j) + g(j, k) + g(k, i)
                rels.append(w)
    # simplify: free reduction, kill generators occurring as single-letter relators,
    # substitute generators occurring exactly once in some relator
    def reduce(w):
        out = []
        for x in w:
            if out and out[-1] == -x:
                out.pop()
            else:
                out.append(x)
        while len(out) >= 2 and out[0] == -out[-1]:
            out = out[1:-1]
        return out
    alive = set(range(1, len(gen) + 1))
    rels = [reduce(r) for r in rels]
    changed = True
    while changed and alive:
        changed = False
        for r in rels:
            if not r:
                continue
            for pos, x in enumerate(r):
                a = abs(x)
                if sum(1 for y in r if abs(y) == a) == 1:
                    # x = inverse of the rest (rotated)
                    rest = r[pos + 1:] + r[:pos]
                    sub = [-y for y in reversed(rest)] if x > 0 else rest
                    def s(w):
                        o = []
                        for y in w:
                            if y == a:
                                o += sub
                            elif y == -a:
                                o += [-z for z in reversed(sub)]
                            else:
                                o.append(y)
                        return o
                    rels = [reduce(s(q)) for q in rels]
                    alive.discard(a)
                    changed = True
                    break
            if changed:
                break
    return not alive

if __name__ == "__main__":
    cert = json.load(open(sys.argv[1]))
    n, m, K = cert["n"], cert["m"], cert["K"]
    from salvetti_morse import pairs
    a = {p: Fraction(v * K) for p, v in zip(pairs(n), cert["a"])}
    eta = {tuple(c): Fraction(e) for c, e in zip(cert["chambers"], cert["eta"])}
    # Morse uses f = sepval + eta with sepval = sum a; the same heights as climb3.
    M = Morse(n, a, eta)
    ok = True
    for C in itertools.permutations(range(n)):
        els = M.asc_poset(C)  # raises on ties among lowest vertices
        b1 = order_complex_homology(els, p=1000003, maxdim=m - 1)
        b2 = order_complex_homology(els, p=32003, maxdim=m - 1)
        good = b1 != [-1] and all(x == 0 for x in b1[:m]) and all(x == 0 for x in b2[:m])
        pt = pi1_trivial(els) if m >= 2 else None
        if not good or (m >= 2 and not pt):
            ok = False
        print(C, len(els), b1[:m], b2[:m], "pi1 trivial" if pt else pt, flush=True)
    print("VERIFIED" if ok else "FAILED")
