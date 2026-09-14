#!/usr/bin/env python3
"""Forward tables of shape ns x nm up to label symmetry, with rule-independent filters.

A forward table is a partition of the cells S x M (row 0 = label 1 of S, column 0 = label 1 of M)
into blocks with at most one cell per row and per column. Relabeling the non-identity labels of S
and of M acts on tables; one representative per orbit is kept (restricted growth string in
row-major order, minimal over the orbit), with its orbit size.

Filters (each excludes strict data at a realized forward table, for every alphabet and rules):
  F1 `strict-left-inverse-memory-meets-memory-ratios`: some block holds a cell of row 0 and a
     cell of another row.
  F3 `private-origin-rows-force-permutation-encoders`: excluded when the block of (0,0) is a
     singleton, no origin block (s,0) meets row 0, and the rows s != 0 order so that each origin
     block only meets later rows (acyclic origin graph).
  F4 `forward-relations-of-a-counterexample-have-a-nonsofic-core`: excluded when the 2-core of the
     relator hypergraph (star spanning relators, identity letters deleted) is empty.
Survivors are written in the format of enum_tables.py of the binary census, so its oracle,
Tietze and certificate scripts apply unchanged.

Usage: enum4.py ns nm survivors.jsonl [count]
"""
import itertools, json, sys


def partitions(ns, nm):
    cells = [(s, m) for s in range(ns) for m in range(nm)]
    assign, rows, cols = [0] * len(cells), [], []

    def rec(i):
        if i == len(cells):
            yield tuple(assign)
            return
        s, m = cells[i]
        for b in range(len(rows)):
            if not (rows[b] >> s) & 1 and not (cols[b] >> m) & 1:
                assign[i] = b
                rows[b] |= 1 << s
                cols[b] |= 1 << m
                yield from rec(i + 1)
                rows[b] &= ~(1 << s)
                cols[b] &= ~(1 << m)
        assign[i] = len(rows)
        rows.append(1 << s)
        cols.append(1 << m)
        yield from rec(i + 1)
        rows.pop()
        cols.pop()
    yield from rec(0)


def rgs(labels):
    seen, out = {}, []
    for x in labels:
        out.append(seen.setdefault(x, len(seen)))
    return tuple(out)


def symmetries(ns, nm):
    for ps in itertools.permutations(range(1, ns)):
        for pm in itertools.permutations(range(1, nm)):
            rs, cs = (0,) + ps, (0,) + pm
            # new cell (rs[s], cs[m]) receives the block of old cell (s, m)
            perm = [0] * (ns * nm)
            for s in range(ns):
                for m in range(nm):
                    perm[rs[s] * nm + cs[m]] = s * nm + m
            yield perm


def blocks(assign, ns, nm):
    bl = {}
    for idx, b in enumerate(assign):
        bl.setdefault(b, []).append(divmod(idx, nm))
    return list(bl.values())


def f1_row_join(bls):
    return any(any(s == 0 for s, _ in b) and any(s != 0 for s, _ in b) for b in bls)


def f3_private_origin(bls, ns):
    of = {c: tuple(b) for b in bls for c in b}
    if len(of[(0, 0)]) != 1:
        return False
    succ = {}
    for s in range(1, ns):
        other = [r for r, _ in of[(s, 0)] if r != s]
        if 0 in other:
            return False
        succ[s] = set(other)
    state = {}

    def cyclic(v):
        state[v] = 1
        for w in succ[v]:
            if state.get(w) == 1 or (w not in state and cyclic(w)):
                return True
        state[v] = 2
        return False
    return not any(v not in state and cyclic(v) for v in succ)


def f4_empty_core(bls):
    def gens(c):
        s, m = c
        return {g for g in ([f"s{s}"] if s else []) + ([f"m{m}"] if m else [])}
    rel = []
    for b in bls:
        for c in b[1:]:
            rel.append(gens(b[0]) | gens(c))
    alive = set(range(len(rel)))
    changed = True
    while changed:
        changed = False
        for i in sorted(alive):
            others = set().union(*(rel[j] for j in alive if j != i)) if len(alive) > 1 else set()
            if rel[i] - others:
                alive.discard(i)
                changed = True
    return not alive


def record(tid, ns, nm, bls, orbit):
    S = ["1"] + [f"s{i}" for i in range(1, ns)]
    M = ["1"] + [f"m{i}" for i in range(1, nm)]
    w = lambda *a: [x for x in a if x != "1"]
    rels = []
    for b in bls:
        s0, m0 = b[0]
        for s, m in b[1:]:
            rels.append([w(S[s0], M[m0]), w(S[s], M[m])])
    return {"id": tid, "ns": ns, "nm": nm, "gens": S[1:] + M[1:], "rels": rels, "orbit": orbit,
            "fwd": {f"{s}|{m}": w(s, m) for s in S for m in M},
            "rev": {f"{m}|{s}": w(m, s) for s in S for m in M},
            "labels": {a: w(a) for a in S + M}}


def main():
    ns, nm, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    count_only = len(sys.argv) > 4 and sys.argv[4] == "count"
    syms = list(symmetries(ns, nm))
    st = {"shape": f"{ns}x{nm}", "partitions": 0, "orbits": 0, "orbit_mass": 0, "fail_F1": 0,
          "excluded_F3": 0, "excluded_F4": 0, "survivors": 0, "survivor_mass": 0}
    with open(out, "w") as fh:
        for a in partitions(ns, nm):
            st["partitions"] += 1
            if count_only:
                continue
            images = {rgs([a[p] for p in perm]) for perm in syms}
            if a != min(images):
                continue
            orbit = len(images)
            st["orbits"] += 1
            st["orbit_mass"] += orbit
            bls = blocks(a, ns, nm)
            if not f1_row_join(bls):
                st["fail_F1"] += 1
                continue
            if f3_private_origin(bls, ns):
                st["excluded_F3"] += 1
                continue
            if f4_empty_core(bls):
                st["excluded_F4"] += 1
                continue
            st["survivors"] += 1
            st["survivor_mass"] += orbit
            fh.write(json.dumps(record(st["survivors"] - 1, ns, nm, bls, orbit)) + "\n")
    print(json.dumps(st))


if __name__ == "__main__":
    main()
