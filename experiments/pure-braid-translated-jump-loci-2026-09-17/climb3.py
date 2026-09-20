"""Incremental simulated-annealing search for a Bestvina--Brady certificate
(fast_morse).  Usage:
    python3 climb3.py n m steps seeds amp 'a_json' tag [init]
init = 'rand' (default) or 'zero' (eta = tiny tie-breaks only).
On success writes cert_n{n}_m{m}_{tag}.json (a, K, eta, per-chamber Betti numbers);
verify_cert.py re-checks such a file from scratch."""
import sys, json, random, time, math
import numpy as np
from fast_morse import Salvetti, pairs, poset_betti

K = 10**6

class State:
    def __init__(self, S, a, m, eta):
        self.S, self.m = S, m
        self.av = np.array([a[p] for p in S.P], dtype=np.int64)
        self.eta = eta.copy()
        N = len(S.ch)
        self.containing = [[] for _ in range(N)]
        for k, (ci, F) in enumerate(S.cells):
            for v in S.stars[F]:
                self.containing[v].append(k)
        self.sep = {}
        for k, (ci, F) in enumerate(S.cells):
            st = S.stars[F]
            self.sep[k] = (S.side[st] != S.side[ci]).astype(np.int64) @ self.av
        self.low = np.array([self.lowest(k) for k in range(len(S.cells))])
        self.asc = [set() for _ in range(N)]
        for k in range(len(S.cells)):
            if S.dim[k] > 0:
                self.asc[self.low[k]].add(k)
        self.defect = np.array([self.cdefect(C) for C in range(N)])

    def lowest(self, k):
        st = self.S.stars[self.S.cells[k][1]]
        f = self.sep[k] + self.eta[st]
        j = np.argmin(f)
        if (f == f[j]).sum() > 1:
            return -1
        return st[j]

    def cdefect(self, C):
        if any(self.low[k] < 0 for k in self.asc[C]):
            return 10**6
        b = poset_betti(self.S, sorted(self.asc[C]), self.m - 1)
        return (self.m + 1) if b is None else sum(b)

    def total(self):
        return int(self.defect.sum()) + 10**6 * int((self.low < 0).sum())

    def move(self, t, delta):
        """change eta[t] by delta; returns undo record"""
        S = self.S
        old_eta = self.eta[t]
        self.eta[t] += delta
        changed = []
        touched = set()
        for k in self.containing[t]:
            nl = self.lowest(k)
            if nl != self.low[k]:
                changed.append((k, self.low[k]))
                if S.dim[k] > 0:
                    if self.low[k] >= 0:
                        self.asc[self.low[k]].discard(k); touched.add(self.low[k])
                    if nl >= 0:
                        self.asc[nl].add(k); touched.add(nl)
                self.low[k] = nl
        old_def = {C: self.defect[C] for C in touched}
        if (self.low < 0).any():
            pass
        for C in touched:
            self.defect[C] = self.cdefect(C) if (self.low[list(self.asc[C])] >= 0).all() else 10**6
        return (t, old_eta, changed, old_def)

    def undo(self, rec):
        t, old_eta, changed, old_def = rec
        S = self.S
        self.eta[t] = old_eta
        for k, ol in reversed(changed):
            nl = self.low[k]
            if S.dim[k] > 0:
                if nl >= 0:
                    self.asc[nl].discard(k)
                if ol >= 0:
                    self.asc[ol].add(k)
            self.low[k] = ol
        for C, d in old_def.items():
            self.defect[C] = d

def search(S, a, m, steps, rng, amp, init="rand", temp0=0.7):
    N = len(S.ch)
    if init.startswith("file:"):
        # warm start from the eta of an earlier certificate / best-state file (same n)
        eta = np.array(json.load(open(init[5:]))["eta"], dtype=np.int64)
        eta += np.array([rng.randrange(0, 1000) for _ in range(N)], dtype=np.int64)
    elif init == "zero":
        eta = np.array([rng.randrange(0, 1000) for _ in range(N)], dtype=np.int64)
    else:
        eta = np.array([rng.randrange(-amp * K, amp * K) for _ in range(N)], dtype=np.int64)
    st = State(S, a, m, eta)
    s = st.total()
    best = (s, st.eta.copy())
    for it in range(steps):
        if s == 0:
            break
        bad = np.nonzero(st.defect)[0]
        if rng.random() < 0.6 and len(bad):
            t = int(rng.choice(list(bad)))
        else:
            t = rng.randrange(N)
        delta = rng.randrange(-amp * K, amp * K) // (1 if rng.random() < 0.5 else 10)
        rec = st.move(t, delta)
        s2 = st.total()
        T = temp0 * (1 - it / steps) + 1e-9
        if s2 <= s or rng.random() < math.exp(-(s2 - s) / T):
            s = s2
            if s < best[0]:
                best = (s, st.eta.copy())
        else:
            st.undo(rec)
    return best, st

if __name__ == "__main__":
    n, m, steps, seeds, amp = map(int, sys.argv[1:6])
    vals = json.loads(sys.argv[6])
    tag = sys.argv[7] if len(sys.argv) > 7 else "x"
    init = sys.argv[8] if len(sys.argv) > 8 else "rand"
    temp0 = float(sys.argv[9]) if len(sys.argv) > 9 else 0.7
    seed0 = int(sys.argv[10]) if len(sys.argv) > 10 else 0
    a = {p: int(v) * K for p, v in zip(pairs(n), vals)}
    t0 = time.time()
    S = Salvetti(n)
    print("cells", len(S.cells), "setup", round(time.time() - t0, 1), "s; a =", vals, flush=True)
    for seed in range(seed0, seed0 + seeds):
        rng = random.Random(seed)
        t0 = time.time()
        (s, eta), st = search(S, a, m, steps, rng, amp, init, temp0)
        print("seed", seed, "best score", s, round(time.time() - t0, 1), "s", flush=True)
        if 0 < s < 10**6:
            stb = State(S, a, m, eta)
            for C in np.nonzero(stb.defect)[0]:
                els = sorted(stb.asc[C])
                print("   bad chamber", list(S.ch[C]), "|Asc|", len(els),
                      "dims", sorted(int(S.dim[k]) for k in els),
                      "betti", poset_betti(S, els, m - 1), flush=True)
            json.dump({"n": n, "m": m, "a": vals, "K": K, "eta": [int(x) for x in eta],
                       "score": int(s)}, open(f"best_n{n}_m{m}_{tag}_seed{seed}.json", "w"))
        if s == 0:
            st2 = State(S, a, m, eta)
            assert st2.total() == 0
            per = {str(list(S.ch[C])): poset_betti(S, sorted(st2.asc[C]), m - 1) for C in range(len(S.ch))}
            json.dump({"n": n, "m": m, "a": vals, "K": K, "eta": [int(x) for x in eta],
                       "chambers": [list(c) for c in S.ch], "betti": per},
                      open(f"cert_n{n}_m{m}_{tag}.json", "w"))
            print("CERTIFIED", flush=True)
            break
