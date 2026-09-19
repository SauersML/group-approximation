#!/usr/bin/env python3
"""Exact Z-elimination of generators through relators with a +-1 entry,
with lazy Markowitz pivoting (a heap keyed by (row length - 1) * (column
count - 1)).

Same contract as census.unit_eliminate: every step is the exact
unimodular substitution g_j = -s * sum_{g != j} piv[g] g coming from a
relator piv with piv[j] = s = +-1, applied to all relators and to the
target vectors.  The quotient Z^ngen / <rels> is unchanged, generator j is
removed, and the targets keep their classes.  Only the pivot ORDER differs
from census.unit_eliminate, so the output is the same abelian group with
the same target classes (up to the choice of surviving basis).
"""
import heapq
import time


def eliminate(ngen, rels, vs, log=print):
    t0 = time.time()
    rows = {}
    for r, v in enumerate(rels):
        v = {g: a for g, a in v.items() if a}
        if v:
            rows[r] = v
    colrows = {}
    for r, v in rows.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    vrows = [dict(v) for v in vs]
    vcol = {}
    for t, v in enumerate(vrows):
        for g in v:
            vcol.setdefault(g, set()).add(t)
    alive = set(range(ngen))
    heap = []

    def push(r):
        v = rows[r]
        best = None
        for g, a in v.items():
            if a == 1 or a == -1:
                c = len(colrows[g])
                if best is None or c < best[0]:
                    best = (c, g)
        if best is not None:
            heapq.heappush(heap, ((len(v) - 1) * (best[0] - 1), r, best[1]))

    for r in rows:
        push(r)
    steps = 0
    while heap:
        cost, r, j = heapq.heappop(heap)
        v = rows.get(r)
        if v is None or v.get(j) not in (1, -1):
            if v is not None:
                push(r)
            continue
        true = (len(v) - 1) * (len(colrows[j]) - 1)
        if true > cost:
            heapq.heappush(heap, (true, r, j))
            continue
        s = v[j]
        piv = v
        del rows[r]
        for g in piv:
            colrows[g].discard(r)
        for q in list(colrows.get(j, ())):
            row = rows[q]
            f = row[j] * s
            for g, b in piv.items():
                nv = row.get(g, 0) - f * b
                if nv:
                    if g not in row:
                        colrows.setdefault(g, set()).add(q)
                    row[g] = nv
                elif g in row:
                    del row[g]
                    colrows[g].discard(q)
            if not row:
                del rows[q]
            else:
                push(q)
        for t in list(vcol.get(j, ())):
            row = vrows[t]
            f = row[j] * s
            for g, b in piv.items():
                nv = row.get(g, 0) - f * b
                if nv:
                    if g not in row:
                        vcol.setdefault(g, set()).add(t)
                    row[g] = nv
                elif g in row:
                    del row[g]
                    vcol[g].discard(t)
        alive.discard(j)
        colrows.pop(j, None)
        vcol.pop(j, None)
        steps += 1
        if steps % 20000 == 0 and log:
            log(f"  fastelim: {steps} pivots, {len(alive)} gens, "
                f"{len(rows)} rows, last cost {cost} [{time.time()-t0:.0f}s]")
    # rows without any unit entry that still hold a unit after all pivots
    # are impossible: every row with a unit entry sits in the heap.
    cols = sorted(alive)
    return cols, [v for v in rows.values() if v], vrows
