"""Homotopy continuation of a Bestvina--Brady certificate toward a twist hyperplane.
a(t) = base + t * dirn, where t runs down a list of values.  At each t, start from the
previous eta.  Record the score of the inherited eta, then anneal (climb3.search,
init = previous eta) and keep the certificate if the score reaches 0.
Usage: python3 continuation.py n m cert.json 'base_json' 'dir_json' 't1,t2,...' steps tag"""
import sys, json, random, time
import numpy as np
from fast_morse import Salvetti, pairs, poset_betti
import climb3
from climb3 import State, K

def main():
    n, m = int(sys.argv[1]), int(sys.argv[2])
    eta = np.array(json.load(open(sys.argv[3]))["eta"], dtype=np.int64)
    base, dirn = json.loads(sys.argv[4]), json.loads(sys.argv[5])
    ts = [float(x) for x in sys.argv[6].split(",")]
    steps, tag = int(sys.argv[7]), sys.argv[8]
    S = Salvetti(n)
    for t in ts:
        vals = [b + t * d for b, d in zip(base, dirn)]
        a = {p: int(round(v * K)) for p, v in zip(pairs(n), vals)}
        st = State(S, a, m, eta)
        s0 = st.total()
        bad = [list(S.ch[C]) for C in np.nonzero(st.defect)[0]]
        print("t", t, "inherited score", s0, "bad", bad[:6], flush=True)
        if s0 > 0:
            json.dump({"eta": [int(x) for x in eta]}, open(f"_warm_{tag}.json", "w"))
            rng = random.Random(int(t * 1000) + 7)
            (s, eta2), _ = climb3.search(S, a, m, steps, rng, 20, init=f"file:_warm_{tag}.json")
            print("   annealed score", s, flush=True)
            if s == 0:
                eta = eta2
            else:
                eta = eta2
                print("   STUCK at t", t, flush=True)
        if s0 == 0 or s == 0:
            st2 = State(S, a, m, eta)
            assert st2.total() == 0
            json.dump({"n": n, "m": m, "a": vals, "K": K, "eta": [int(x) for x in eta],
                       "chambers": [list(c) for c in S.ch]},
                      open(f"cert_n{n}_m{m}_{tag}_t{t}.json", "w"))
            print("   CERTIFIED at t", t, flush=True)

if __name__ == "__main__":
    main()
