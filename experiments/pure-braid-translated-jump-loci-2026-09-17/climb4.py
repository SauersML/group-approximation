"""Annealing search in which the character moves too, inside a linear subspace.

climb3.py fixes the character a and searches over eta.  Here a also moves, inside
    { sum a = 0,  c_A(a) = 0 for the given strand sets A }.
Any certificate found proves [chi] in Sigma^m(P_n) for the final a, which lies on the
requested twist hyperplanes.  Such a character is automatically non-resonant, because
Sigma^m misses R^{<=m}.  a-moves add d*(e_p - e_q) for two pairs p, q, chosen so that
the move preserves every constraint: both pairs lie in exactly the same sets A.
Usage: python3 climb4.py n m steps seeds amp 'a_json' 'A_json_list' tag [pa]
   pa = probability of an a-move (default 0.1).  a is scaled by K as in climb3."""
import sys, json, random, time, math, itertools
import numpy as np
from fast_morse import Salvetti, pairs, poset_betti
from climb3 import State, K

class AState(State):
    def __init__(self, S, a, m, eta):
        super().__init__(S, a, m, eta)
        self.sepmat = {}
        for k, (ci, F) in enumerate(S.cells):
            st = S.stars[F]
            self.sepmat[k] = (S.side[st] != S.side[ci]).astype(np.int64)

    def amove(self, p, q, d):
        S = self.S
        old = (self.av.copy(), dict(self.sep), self.low.copy(), [set(x) for x in self.asc], self.defect.copy())
        self.av[p] += d; self.av[q] -= d
        touched = set()
        for k in range(len(S.cells)):
            self.sep[k] = self.sepmat[k] @ self.av
            nl = self.lowest(k)
            if nl != self.low[k]:
                if S.dim[k] > 0:
                    if self.low[k] >= 0:
                        self.asc[self.low[k]].discard(k); touched.add(int(self.low[k]))
                    if nl >= 0:
                        self.asc[nl].add(k); touched.add(int(nl))
                self.low[k] = nl
        for C in touched:
            self.defect[C] = self.cdefect(C) if (self.low[list(self.asc[C])] >= 0).all() else 10**6
        return ("a", old)

    def undo(self, rec):
        if rec[0] == "a":
            self.av, self.sep, self.low, self.asc, self.defect = rec[1]
        else:
            super().undo(rec)

def main():
    n, m, steps, seeds, amp = map(int, sys.argv[1:6])
    vals = json.loads(sys.argv[6])
    zeroA = [tuple(sorted(A)) for A in json.loads(sys.argv[7])]
    tag = sys.argv[8]
    pa = float(sys.argv[9]) if len(sys.argv) > 9 else 0.1
    P = pairs(n)
    # pairs grouped by membership pattern in the zero sets: moves within a class keep all c_A
    pattern = {i: tuple(set(p) <= set(A) for A in zeroA) for i, p in enumerate(P)}
    classes = {}
    for i, pat in pattern.items():
        classes.setdefault(pat, []).append(i)
    movable = [c for c in classes.values() if len(c) >= 2]
    a = {p: int(v) * K for p, v in zip(P, vals)}
    S = Salvetti(n)
    print("cells", len(S.cells), "a =", vals, "zero sets", zeroA, "move classes", movable, flush=True)
    for seed in range(seeds):
        rng = random.Random(1000 + seed)
        t0 = time.time()
        N = len(S.ch)
        eta = np.array([rng.randrange(-amp * K, amp * K) for _ in range(N)], dtype=np.int64)
        st = AState(S, a, m, eta)
        s = st.total(); best = (s, st.eta.copy(), st.av.copy())
        for it in range(steps):
            if s == 0:
                break
            if rng.random() < pa:
                cl = rng.choice(movable)
                p, q = rng.sample(cl, 2)
                d = rng.randrange(-5 * K, 5 * K)
                rec = st.amove(p, q, d)
            else:
                bad = np.nonzero(st.defect)[0]
                t = int(rng.choice(list(bad))) if (rng.random() < 0.6 and len(bad)) else rng.randrange(N)
                delta = rng.randrange(-amp * K, amp * K) // (1 if rng.random() < 0.5 else 10)
                rec = st.move(t, delta)
            s2 = st.total()
            T = 0.7 * (1 - it / steps) + 1e-9
            if s2 <= s or rng.random() < math.exp(-(s2 - s) / T):
                s = s2
                if s < best[0]:
                    best = (s, st.eta.copy(), st.av.copy())
            else:
                st.undo(rec)
        s, eta, av = best
        print("seed", seed, "best score", s, round(time.time() - t0, 1), "s", flush=True)
        if s == 0:
            g = math.gcd(*[int(x) for x in av], *[int(x) for x in eta])
            aint = [int(x) for x in av]
            st2 = State(S, {p: v for p, v in zip(P, aint)}, m, eta)
            assert st2.total() == 0
            json.dump({"n": n, "m": m, "a": aint, "K": 1, "eta": [int(x) for x in eta],
                       "chambers": [list(c) for c in S.ch], "zero_sets": [list(A) for A in zeroA]},
                      open(f"cert_n{n}_m{m}_{tag}.json", "w"))
            print("CERTIFIED a/K =", [x / K for x in aint], flush=True)
            break

if __name__ == "__main__":
    main()
