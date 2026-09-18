"""SAT search v4: arbitrary valence, legality enforced lazily (CEGAR).

Built-in derived constraint (sign-parity lemma, see the -proof note): for a positive
automorphism every sign-change corner of the boundary sits at a bivalent vertex.
This is a consequence of (2),(3) and parity, added explicitly for propagation.

usage: python3 sat4.py '<phi json>' m kmax maxlen maxdarts tlimit out.json
"""
import sys, time, json
from ffold import *
from search2 import legal_words_dfs
from search3 import power, BoundaryK, lift

def sign(x):
    return 1 if x.islower() else -1

def build4(B, g, parity=True):
    N = B.N
    var = {}
    top = [0]
    cand = [[q for q in range(N) if B.label[q] == inv(B.label[d])] for d in range(N)]
    for d in range(N):
        for q in cand[d]:
            key = (min(d, q), max(d, q))
            if key not in var:
                top[0] += 1; var[key] = top[0]
    lit = lambda d, q: var.get((min(d, q), max(d, q)))
    cl = []
    forb = set()
    for d in range(N):
        for q in cand[d]:
            n = B.nxt[q]                                   # sigma(d) = n
            if q == B.prv[d] or q == B.nxt[d]: forb.add(lit(d, q))
            if g[B.label[d]] == g[B.label[n]]: forb.add(lit(d, q))       # legality, adjacent
            if B.kind[d] == "-" and B.kind[q] == "-": forb.add(lit(d, q))  # (4) edge
            if B.kind[d] == "-" and B.kind[n] == "-": forb.add(lit(d, q))  # (4) vertex, adjacent
            if B.fdart[d] and B.fdart[n]: forb.add(lit(d, q))              # (3) adjacent
    cl += [[-l] for l in forb]
    t = top[0]
    for d in range(N):
        lits = [lit(d, q) for q in cand[d]]
        if not lits: return None
        enc = CardEnc.equals(lits=lits, bound=1, top_id=t, encoding=EncType.seqcounter)
        t = max(t, enc.nv); cl += enc.clauses
    def bivalent_clauses(c):
        pc = B.prv[c]
        for q in cand[c]:
            l2 = lit(B.nxt[q], pc)
            cl.append([-lit(c, q)] + ([l2] if l2 else []))
    for d in range(N):
        if B.fdart[d]: bivalent_clauses(d)                                  # (2)
        elif parity and sign(B.label[B.prv[d]]) != sign(B.label[d]): bivalent_clauses(d)
    ys = []
    for d in range(N):
        t += 1; y = t; ys.append(y)
        pd = B.prv[d]
        for q in cand[d]:
            l2 = lit(B.nxt[q], pd)
            if l2: cl.append([-y, -lit(d, q), -l2])
    cl.append(ys)
    return cl, var, lit, t

def orbits(B, p):
    seen = set(); res = []
    for d in range(B.N):
        if d in seen: continue
        o = [d]; e = B.nxt[p[d]]
        while e != d:
            o.append(e); e = B.nxt[p[e]]
        seen.update(o); res.append(o)
    return res

def solve4(B, g, parity=True, maxiter=20000):
    r = build4(B, g, parity)
    if r is None: return None, 0
    cl, var, lit, t = r
    s = Cadical153(bootstrap_with=cl)
    it = 0
    while it < maxiter:
        it += 1
        if not s.solve(): return False, it
        model = set(l for l in s.get_model() if l > 0)
        p = {}
        for (d, q), l in var.items():
            if l in model: p[d] = q; p[q] = d
        added = 0
        for o in orbits(B, p):
            L = len(o)
            for i in range(L):
                for j in range(i + 1, L):
                    a, b = o[i], o[j]
                    bad = g[B.label[a]] == g[B.label[b]] or (B.kind[a] == "-" and B.kind[b] == "-")
                    if not bad: continue
                    # chain of sigma steps i -> j (or j -> i, whichever shorter)
                    idxs = range(i, j) if j - i <= L - (j - i) else list(range(j, L)) + list(range(0, i))
                    s.add_clause([-lit(o[k], p[o[k]]) for k in idxs])
                    added += 1
        if added == 0:
            return p, it
    return None, it

def verify4(B, p, g, nunroll=2):
    N = B.N; rep = {}
    assert all(p[p[d]] == d and p[d] != d for d in range(N))
    assert all(B.label[p[d]] == inv(B.label[d]) for d in range(N))
    vs = orbits(B, p)
    rep["valences"] = sorted(len(o) for o in vs)
    assert all(len(o) >= 2 for o in vs)
    for o in vs:
        assert len({g[B.label[e]] for e in o}) == len(o), "illegal vertex"
        assert sum(1 for e in o if B.kind[e] == "-") <= 1, "(4) vertex"
        nf = sum(1 for e in o if B.fdart[e])
        assert nf <= 1, "(3)"
        if nf: assert len(o) == 2, "(2)"
    for d in range(N):
        assert not (B.kind[d] == "-" and B.kind[p[d]] == "-"), "(4) edge"
    V = len(vs); E = N // 2
    rep["V"], rep["E"], rep["chi"] = V, E, V - E
    vid = {e: i for i, o in enumerate(vs) for e in o}
    uf = list(range(V))
    def find(x):
        while uf[x] != x: uf[x] = uf[uf[x]]; x = uf[x]
        return x
    for d in range(N): uf[find(vid[d])] = find(vid[p[d]])
    rep["components_X"] = len({find(x) for x in range(V)})
    rep["unroll"] = unroll_check(B, p, g, nunroll)
    return rep

def main(phi0, m, kmax, maxlen, maxdarts, tlimit, out):
    phi = power(phi0, m)
    g = gate_of(phi)
    try: cert = certify_fully_irreducible_atoroidal(phi0)
    except Exception as e: cert = repr(e)
    print("phi0", phi0, "m", m, "phi", phi, cert, "gates", "".join(g[d] for d in "abcABC"), flush=True)
    words = sorted(legal_words_dfs(g, maxlen, True), key=len)
    cands = [(w, k) for w in words for k in (1, 2, 3, 5) if k <= kmax
             if k * (len(w) + len(apply(phi, w))) <= maxdarts]
    cands.sort(key=lambda c: c[1] * (len(c[0]) + len(apply(phi, c[0]))))
    print("candidates", len(cands), flush=True)
    t0 = time.time(); tried = 0; iters = 0
    for (w, k) in cands:
        B = BoundaryK(phi, w, k)
        tried += 1
        pr, it = solve4(B, g)
        iters += it
        if not pr:
            if time.time() - t0 > tlimit: break
            continue
        Bt, pt = lift(B, pr, w, k)
        rep = verify4(Bt, pt, g, nunroll=2)
        print("FOUND", w, k, rep, flush=True)
        json.dump({"phi0": phi0, "power": m, "phi": phi, "certificate": cert, "w": w, "k": k,
                   "base_boundary": [x for x, _ in B.words], "base_pairing": [pr[d] for d in range(B.N)],
                   "cover_pairing": [pt[d] for d in range(Bt.N)], "report": rep},
                  open(out, "w"), indent=1)
        return
    print("none; tried", tried, "of", len(cands), "iters", iters, "time", round(time.time() - t0, 1), flush=True)

if __name__ == "__main__":
    main(json.loads(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]),
         int(sys.argv[5]), float(sys.argv[6]), sys.argv[7])
