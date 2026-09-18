"""Certificate search: legal f-folded fatgraphs with one or two d^- circles."""
import itertools, sys, time, json
from ffold import *

def canon_cyc(w):
    return min(w[i:]+w[:i] for i in range(len(w)))
def ab(w):
    return tuple(w.count(x)-w.count(inv(x)) for x in POS)

def legal_words_dfs(g, maxlen, zero_only):
    res = set()
    def rec(w, h):
        L = len(w)
        if L >= 2 and legal_turn(g, w[-1], w[0]) and w[-1] != inv(w[0]):
            if (not zero_only) or h == (0,0,0):
                c = canon_cyc(w)
                if c == w and not any(L % k == 0 and c == c[:k]*(L//k) for k in range(1, L)):
                    res.add(c)
        if L == maxlen: return
        for x in "abcABC":
            if L and (x == inv(w[-1]) or not legal_turn(g, w[-1], x)): continue
            if L and x < w[0]: continue   # canonical rotation starts with min letter
            i = "abc".find(x.lower()); s = 1 if x.islower() else -1
            hh = list(h); hh[i] += s
            if zero_only and sum(abs(t) for t in hh) > maxlen - L - 1: continue
            rec(w + x, tuple(hh))
    rec("", (0,0,0))
    return res

def main(phi, maxlen1, maxlen2, maxdarts, tlimit, out):
    g = gate_of(phi)
    cert = certify_fully_irreducible_atoroidal(phi)
    print("phi", phi, cert, "gates", "".join(g[d] for d in "abcABC"), flush=True)
    singles = sorted(legal_words_dfs(g, maxlen1, True), key=lambda w: (len(apply(phi,w))+len(w), w))
    cands = [(w,) for w in singles]
    if maxlen2:
        allw = sorted(legal_words_dfs(g, maxlen2, False), key=len)
        byab = {}
        for w in allw: byab.setdefault(ab(w), []).append(w)
        for w in allw:
            if ab(w) == (0,0,0): continue
            for v in byab.get(tuple(-t for t in ab(w)), []):
                if w <= v: cands.append((w, v))
    cands = [c for c in cands if sum(len(w)+len(apply(phi,w)) for w in c) <= maxdarts]
    cands.sort(key=lambda ws: sum(len(w)+len(apply(phi,w)) for w in ws))
    print("candidates", len(cands), flush=True)
    t0 = time.time(); tried = 0; unsat_biv = 0
    for ws in cands:
        B = Boundary(phi, list(ws))
        tried += 1
        p = solve(B)
        if p is None or p is False:
            if time.time() - t0 > tlimit: break
            continue
        rep = verify(B, p, g, nunroll=3)
        print("FOUND", ws, [w for w,k in B.words], rep, flush=True)
        json.dump({"phi": phi, "certificate": cert, "minus": ws, "boundary": [w for w,k in B.words],
                   "pairing": [p[d] for d in range(B.N)], "report": rep}, open(out, "w"), indent=1)
        return
    print("none; tried", tried, "of", len(cands), "time", time.time()-t0, flush=True)

if __name__ == "__main__":
    phi = json.loads(sys.argv[1])
    main(phi, int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5]), sys.argv[6])
