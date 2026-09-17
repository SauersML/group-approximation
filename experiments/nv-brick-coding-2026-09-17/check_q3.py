"""Verify (A1)-(A3) for the q = 3 triangle presentations in tp_q3.json."""
import json
from tp_q3 import LINES, n

ex = json.load(open("tp_q3.json"))["examples"]
for k, (lam, T) in enumerate(ex):
    T = set(map(tuple, T))
    assert all((y, z, x) in T for (x, y, z) in T)  # (A2)
    nxt = {}
    for (x, y, z) in T:
        assert (x, y) not in nxt  # (A3)
        nxt[(x, y)] = z
    for x in range(n):
        for y in range(n):
            assert ((x, y) in nxt) == (y in LINES[lam[x]])  # (A1)
    print(f"q3 T{k}: lam={lam}; |T| = {len(T)}; (A1)-(A3) hold")
