"""Hill-climb over eta (fast_morse).  Usage:
    python3 climb2.py n m steps seeds amp 'a_json'
a_json: list of integers a_ij in pairs(n) order.  Prints CERTIFIED and writes the
certificate (a, eta, per-chamber Betti numbers) to cert_n{n}_m{m}_<tag>.json."""
import sys, json, random, time
import numpy as np
from fast_morse import Salvetti, pairs, poset_betti

K = 10**6  # scale: a -> K a; eta random with low bits for genericity

def evaluate(S, a, eta, m, chambers=None):
    low = S.lowest(a, eta)
    per = {}
    tot = 0
    for C in (chambers if chambers is not None else range(len(S.ch))):
        els = S.asc(low, C)
        b = poset_betti(S, els, m - 1)
        d = (m + 1) if b is None else sum(b)
        per[C] = (d, b)
        tot += d
    return tot, per

def climb(S, a, m, steps, rng, amp):
    N = len(S.ch)
    eta = np.array([rng.randrange(-amp * K, amp * K) for _ in range(N)], dtype=np.int64)
    try:
        s, per = evaluate(S, a, eta, m)
    except ValueError:
        return None, eta, None
    for it in range(steps):
        if s == 0:
            break
        bad = [C for C in per if per[C][0] > 0]
        C0 = rng.choice(bad)
        new = eta.copy()
        tgt = C0 if rng.random() < 0.5 else rng.randrange(N)
        new[tgt] += rng.randrange(-amp * K, amp * K)
        try:
            s2, per2 = evaluate(S, a, new, m)
        except ValueError:
            continue
        if s2 <= s:
            eta, s, per = new, s2, per2
    return s, eta, per

if __name__ == "__main__":
    n, m, steps, seeds, amp = map(int, sys.argv[1:6])
    vals = json.loads(sys.argv[6])
    tag = sys.argv[7] if len(sys.argv) > 7 else "x"
    a = {p: int(v) * K for p, v in zip(pairs(n), vals)}
    t = time.time()
    S = Salvetti(n)
    print("cells", len(S.cells), "setup", round(time.time() - t, 1), "s; a =", vals, flush=True)
    for seed in range(seeds):
        rng = random.Random(seed)
        t = time.time()
        s, eta, per = climb(S, a, m, steps, rng, amp)
        print("seed", seed, "score", s, round(time.time() - t, 1), "s", flush=True)
        if s == 0:
            print("CERTIFIED")
            out = {"n": n, "m": m, "a": vals, "K": K, "eta": [int(x) for x in eta],
                   "chambers": [list(c) for c in S.ch],
                   "betti": {str(list(S.ch[C])): per[C][1] for C in per}}
            json.dump(out, open(f"cert_n{n}_m{m}_{tag}.json", "w"))
            break
