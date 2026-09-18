"""Confluence + relator + sphere-size checks for q=3 presentations (expected spheres 1, 26, 390, 4914:
N(m,n) = 13*9^(m-1) * 12*9^(n-1), summed over m+n = r, with N(r,0) = N(0,r) = 13*9^(r-1))."""
import json, sys
from a2group import A2Group
Ts = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "presentations_q3.json"))
R = int(sys.argv[2]) if len(sys.argv) > 2 else 3
bad = 0
for i, T in enumerate(Ts):
    G = A2Group([tuple(t) for t in T])
    ok, npairs = G.check_confluence()
    rel = G.check_relators()
    sizes = [len(l) for l in G.ball(R)]
    good = ok and rel and sizes == [1, 26, 390, 4914][:R + 1]
    bad += not good
    print(f"T{i} confluent={ok} pairs={npairs} relators={rel} spheres={sizes}", flush=True)
print("ALL OK" if bad == 0 else f"{bad} FAILURES")
