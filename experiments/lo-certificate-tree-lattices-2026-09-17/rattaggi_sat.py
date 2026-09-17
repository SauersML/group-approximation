"""SAT search for a non-left-orderability certificate of Rattaggi's simple group
Lambda = ker(Gamma -> Z/2 x Z/2) (arXiv:math/0507363), and of Gamma itself."""
import sys, time, itertools
from bmw import BMW, RATTAGGI_INCOHERENT
from lo_sat import CNFBuilder, write_dimacs

def elements(G, amax, bmax, L, parity):
    out = []
    for la in range(0, amax + 1):
        for lb in range(0, bmax + 1):
            if la + lb > L or la + lb == 0:
                continue
            if parity and (la % 2 or lb % 2):
                continue
            for A in G.reduced_words(G.m, la):
                for B in G.reduced_words(G.n, lb):
                    out.append((A, B))
    return out

def build(G, L, parity, short):
    els = elements(G, L, L, L, parity)
    S = set(els)
    cb = CNFBuilder(els, G.inv)
    shorts = [g for g in els if len(g[0]) + len(g[1]) <= short]
    t = time.time()
    for s in shorts:
        for q in els:
            r = G.mul(s, q)
            if r in S:
                cb.add_triple(s, q, r)
            r = G.mul(q, s)
            if r in S:
                cb.add_triple(q, s, r)
    return els, cb, time.time() - t

if __name__ == "__main__":
    L = int(sys.argv[1]); parity = sys.argv[2] == "lambda"; short = int(sys.argv[3])
    G = BMW(6, 5, RATTAGGI_INCOHERENT)
    els, cb, tb = build(G, L, parity, short)
    print("L=%d group=%s short=%d elements=%d vars=%d clauses=%d build=%.1fs" % (L, sys.argv[2], short, len(els), cb.nv, len(cb.clauses), tb)); sys.stdout.flush()
    res, model, ts = cb.solve()
    print("SAT" if res else "UNSAT", "solve=%.1fs" % ts)
