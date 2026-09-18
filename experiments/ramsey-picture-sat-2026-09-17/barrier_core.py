"""Locate the obstruction to the fixed 1/3 barrier: an (iteratively shrunk) UNSAT core of rows
g in I_n (one selector per row), with the word lengths of the core elements and of their
B_1-neighbours.  usage: python3 barrier_core.py {F|F2|Z2} n
"""
import json
import sys
from collections import Counter

from pysat.solvers import Glucose4

from ramsey_sat import setup
from third_barrier import FAM


def core(name, n):
    dist, idx, interior, k = setup(name, n)
    N = len(dist)
    elems = list(dist)  # idx[g] = position + 1
    forb = [P for P in range(1 << k) if P not in FAM]
    sel = {}
    s = Glucose4()
    for r, row in enumerate(interior):
        sv = N + 1 + r
        sel[sv] = r
        for P in forb:
            s.add_clause([(-v if P >> i & 1 else v) for i, v in enumerate(row)] + [-sv])
    assum = list(sel)
    assert not s.solve(assumptions=assum)
    cur = sorted(s.get_core())
    for _ in range(20):  # shrink by re-solving on the core
        assert not s.solve(assumptions=cur)
        nxt = sorted(s.get_core())
        if len(nxt) >= len(cur):
            break
        cur = nxt
    # deletion-based minimisation (MUS) if the core is small enough
    if len(cur) <= 3000:
        i = 0
        while i < len(cur):
            trial = cur[:i] + cur[i + 1:]
            if not s.solve(assumptions=trial):
                cur = sorted(set(s.get_core()) & set(trial)) or trial
            else:
                i += 1
    s.delete()
    rows = [sel[v] for v in cur]
    # the element g of row r: the entry for a = e (A[0] = identity)
    gl = Counter(dist[elems[interior[r][0] - 1]] for r in rows)
    touched = sorted({v for r in rows for v in interior[r]})
    tl = Counter(dist[elems[v - 1]] for v in touched)
    return {"group": name, "n": n, "core_rows": len(rows),
            "core_g_lengths": dict(sorted(gl.items())),
            "touched_elements": len(touched), "touched_lengths": dict(sorted(tl.items())),
            "rows": rows}


if __name__ == "__main__":
    r = core(sys.argv[1], int(sys.argv[2]))
    print(json.dumps({k: v for k, v in r.items() if k != "rows"}), flush=True)
    json.dump(r, open(f"barrier_core_{sys.argv[1]}_n{sys.argv[2]}.json", "w"), indent=1)
