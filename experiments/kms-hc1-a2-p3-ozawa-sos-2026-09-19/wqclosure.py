"""wq-normal closure of H_0 = <t> (t of infinite order) in Gamma_3, every step proven exactly.

H is kept as a list of generator words gens (H_0 = <gens[0]>).  Step: find x in the Q-ball and
infinite-order y, k in H (explicit words) with y x = x k in Q; prove y x k^-1 x^-1 = 1 in Gamma_3
(tube certificate) and append x to gens.  Then y in xHx^-1 cap H, so that intersection is infinite,
and H_{i+1} = <H_i, x> is a legitimate next term of a wq-normal chain (Popa; Peterson-Thom).
If a, b, c all enter H, then <t> ~ Z is wq-normal in Gamma_3, hence beta_1^(2)(Gamma_3) = 0.
Elements of H inside the Q-ball are enumerated as products of generator words; a product is
replaced by the ball's BFS word only after the equality is proven by a tube certificate."""
import sys, time, numpy as np
from qball import Q
from tube import W, inv_word, LET
from qsearch import QBall, prove, wstr

def left_all(QB, w):
    """keys of w*x for every ball element x."""
    q = QB.q; N = len(QB.keys); kI, kA = QB.elem(w)
    LI = np.zeros(N, dtype=np.int64); LA = np.zeros((N, q.r), dtype=np.int16)
    LI[QB.root] = kI[0]; LA[QB.root] = kA[0]
    for d in range(1, int(QB.dist.max()) + 1):
        lay = np.nonzero(QB.dist == d)[0]
        for s in range(6):
            g = lay[QB.last[lay] == s]
            if len(g): I1, A1 = QB.apply(LI[QB.par[g]], LA[QB.par[g]], s); LI[g] = I1; LA[g] = A1
    return q.key(LI, LA)

def right_all(QB, w):
    return QB.q.key(*QB.apply_word(QB.I, QB.A, w))

def run(qfile, r, t, maxlen, rounds, log=print):
    t0 = time.time(); q = Q(qfile); QB = QBall(q, r); N = len(QB.keys)
    idx = {int(k): i for i, k in enumerate(QB.keys)}
    key = lambda w: int(q.key(*QB.elem(w))[0])
    gens = [t]; steps = [('start', wstr(t))]; target = {nm: key(W(nm)) for nm in 'abc'}
    for rnd in range(rounds):
        # enumerate H cap ball: BFS over products with generators (proven short words)
        Hb = {key([]): []}; fr = [[]]
        while fr:
            nf = []
            for h in fr:
                for g in gens + [inv_word(g) for g in gens]:
                    p = h + g; kp = key(p)
                    if kp in Hb or kp not in idx: continue
                    wb = QB.word(idx[kp])
                    if wb != p and prove(q, p + inv_word(wb), (2, 3)) is None: continue
                    Hb[kp] = wb; nf.append(wb)
            fr = nf
        inH = [nm for nm, k in target.items() if k in Hb]
        infs = [w for w in Hb.values() if 0 < len(w) <= maxlen and QB.infinite(w)]
        log(f"round {rnd}: gens {len(gens)}, |H cap B_{r}| = {len(Hb)}, short infinite {len(infs)}, in H: {inH} [{time.time()-t0:.0f}s]")
        if len(inH) == 3: return gens, steps, True
        Lk = {wstr(y): left_all(QB, y) for y in infs}; Rk = {wstr(k): right_all(QB, k) for k in infs}
        newx = None
        for ys, L in Lk.items():
            for ks, Rr in Rk.items():
                for x in np.nonzero(L == Rr)[0].tolist():
                    if int(QB.keys[x]) in Hb: continue
                    wx = QB.word(x); y, k = W(ys), W(ks)
                    rho = prove(q, y + wx + inv_word(k) + inv_word(wx))
                    if rho is None: continue
                    newx = (wx, ys, ks, rho); break
                if newx: break
            if newx: break
        if newx is None: log("  no new element: closure stalls inside the ball"); return gens, steps, False
        gens.append(newx[0]); steps.append(('conj', wstr(newx[0]), newx[1], newx[2], newx[3]))
        log(f"  + x = {wstr(newx[0])}:  {newx[1]} x = x {newx[2]}  (tube rho={newx[3]})")
    return gens, steps, False

if __name__ == '__main__':
    gens, steps, ok = run(sys.argv[1], int(sys.argv[2]), W(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
    print("RESULT", ok); [print("  ", s) for s in steps]
