"""Certificate search, version 3: k copies of d^- = w, one d^+ circle = f(w^k)^{-1},
optionally for a power f^m.  A SAT solution X is lifted to a k-fold cover X~ whose
boundary is k circles w^k and k circles f(w^k)^{-1}; X~ is then re-verified from
scratch in the standard one-to-one format (verify + unroll_check of ffold.py).

usage: python3 search3.py '<phi json>' m kmax maxlen maxdarts tlimit out.json
"""
import sys, time, json
from ffold import *
from search2 import legal_words_dfs

def power(phi, m):
    res = {x: x for x in POS}
    for _ in range(m):
        res = {x: apply(phi, res[x]) for x in POS}
    return res

class BoundaryK(Boundary):
    """k circles w (kind '-'), one circle f(w^k)^{-1} (kind '+')."""
    def __init__(self, phi, w, k):
        self.phi = phi
        self.words = []; self.label = []; self.nxt = []; self.prv = []
        self.kind = []; self.fdart = []; self.circle = []
        for ci in range(k):
            self._add(w, "-", set(), ci)
        blocks = [phi[x] if x.islower() else inv_word(phi[x.lower()]) for x in w * k]
        plus = "".join(inv_word(b) for b in reversed(blocks))
        starts = set(); pos = 0
        for b in reversed(blocks):
            starts.add(pos); pos += len(b)
        self._add(plus, "+", starts, "P")
        self.N = len(self.label)

def solve_mod_p(rows, rhs, nvars, P):
    """Gaussian elimination over GF(P); returns a solution or None."""
    A = [list(r) + [b] for r, b in zip(rows, rhs)]
    piv = []; r = 0
    for c in range(nvars):
        pr = next((i for i in range(r, len(A)) if A[i][c] % P), None)
        if pr is None: continue
        A[r], A[pr] = A[pr], A[r]
        iv = pow(A[r][c], P - 2, P)
        A[r] = [(x * iv) % P for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] % P:
                f = A[i][c]
                A[i] = [(x - f * y) % P for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    for i in range(r, len(A)):
        if A[i][-1] % P: return None
    sol = [0] * nvars
    for i, c in enumerate(piv):
        sol[c] = A[i][-1]
    return sol

def lift(B, p, w, k):
    """k-fold cover; returns (Btilde, ptilde) in standard format Boundary(phi,[w^k]*k)."""
    N = B.N
    reps = [d for d in range(N) if d < p[d]]
    idx = {d: i for i, d in enumerate(reps)}
    def coef(d):
        return (idx[d], 1) if d in idx else (idx[p[d]], -1)
    rows, rhs = [], []
    circles = {}
    for d in range(N):
        circles.setdefault(B.circle[d][0], []).append(d)
    for ci in range(k):
        row = [0] * len(reps)
        for d in circles[ci]:
            i, s = coef(d); row[i] += s
        rows.append(row); rhs.append(1)
    if k == 1:
        h = [0] * len(reps)
    else:
        h = solve_mod_p(rows, rhs, len(reps), k)   # k prime
        assert h is not None
    hol = lambda d: (h[idx[d]] if d in idx else -h[idx[p[d]]]) % k
    Bt = Boundary(B.phi, [w * k] * k)
    Lw = len(w); Lp = len(circles["P"])
    # map lifted darts (d, j) -> index in Bt
    pos = {}
    # minus circles: circle ci of Bt = lift of original minus circle ci starting at sheet 0
    Lt = len(w) * k
    for ci in range(k):
        base = ci * (Lt + Lp)
        d0 = circles[ci][0]; j = 0; d = d0
        for t in range(Lt):
            pos[(d, j)] = base + t
            j = (j + hol(d)) % k; d = B.nxt[d]
        assert (d, j) == (d0, 0)
    for ci in range(k):
        base = ci * (Lt + Lp) + Lt
        d0 = circles["P"][0]; j = ci; d = d0
        for t in range(Lp):
            pos[(d, j)] = base + t
            j = (j + hol(d)) % k; d = B.nxt[d]
        assert (d, j) == (d0, ci), "plus circle does not lift trivially"
    assert len(pos) == Bt.N
    inv_pos = {v: kk for kk, v in pos.items()}
    pt = {}
    for t in range(Bt.N):
        d, j = inv_pos[t]
        pt[t] = pos[(p[d], (j + hol(d)) % k)]
        assert Bt.label[t] == B.label[d] and Bt.fdart[t] == B.fdart[d] and Bt.kind[t] == B.kind[d]
    return Bt, pt

def main(phi0, m, kmax, maxlen, maxdarts, tlimit, out):
    phi = power(phi0, m)
    g = gate_of(phi)
    try:
        cert = certify_fully_irreducible_atoroidal(phi0)
    except Exception as e:
        cert = repr(e)
    print("phi0", phi0, "m", m, "phi", phi, cert, "gates", "".join(g[d] for d in "abcABC"), flush=True)
    words = sorted(legal_words_dfs(g, maxlen, True), key=lambda w: (len(w), w))
    cands = [(w, k) for w in words for k in range(1, kmax + 1) if k in (1, 2, 3, 5)
             if k * (len(w) + len(apply(phi, w))) <= maxdarts]
    cands.sort(key=lambda c: c[1] * (len(c[0]) + len(apply(phi, c[0]))))
    print("candidates", len(cands), flush=True)
    t0 = time.time(); tried = 0
    for (w, k) in cands:
        B = BoundaryK(phi, w, k)
        tried += 1
        pr = solve(B)
        if pr is None or pr is False:
            if time.time() - t0 > tlimit: break
            continue
        Bt, pt = lift(B, pr, w, k)
        rep = verify(Bt, pt, g, nunroll=2)
        print("FOUND", w, k, rep, flush=True)
        json.dump({"phi0": phi0, "power": m, "phi": phi, "certificate": cert, "w": w, "k": k,
                   "base_boundary": [x for x, _ in B.words], "base_pairing": [pr[d] for d in range(B.N)],
                   "cover_minus": [w * k] * k, "cover_pairing": [pt[d] for d in range(Bt.N)],
                   "report": rep}, open(out, "w"), indent=1)
        return
    print("none; tried", tried, "of", len(cands), "time", round(time.time() - t0, 1), flush=True)

if __name__ == "__main__":
    main(json.loads(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]),
         int(sys.argv[5]), float(sys.argv[6]), sys.argv[7])
