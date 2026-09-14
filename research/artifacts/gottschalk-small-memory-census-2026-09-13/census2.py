#!/usr/bin/env python3
"""Independent re-implementation of census.py (pure python, different encoding).

For every forward table T (rook-independent partition of S x M) whose presented group
P(T) realizes exactly T with distinct labels (per the certified oracle output), and for
every rule mu: A^M -> A:
  * decide whether some nu satisfies Dec(T): relay tuples must determine p(1,1);
  * if so, decide whether some extension nu of the forced partial decoder breaks Enc at
    the reverse table realized in P(T), i.e. whether some T_r^P-constant assignment q
    has mu((nu(q(m, .)))_m) != q(1, 1).
A hit is realized strict data, hence a group P(T) that is not surjunctive.
Prints one JSON summary; hits are listed in full.
"""
import itertools, json, sys

def uf_partition(cells, rels, fwd):
    word_to_cell = {tuple(w): c for c, w in fwd.items()}
    parent = {c: c for c in cells}
    def find(c):
        while parent[c] != c:
            parent[c] = parent[parent[c]]
            c = parent[c]
        return c
    for a, b in rels:
        parent[find(word_to_cell[tuple(a)])] = find(word_to_cell[tuple(b)])
    blocks = {}
    for c in cells:
        blocks.setdefault(find(c), set()).add(c)
    return {frozenset(b) for b in blocks.values()}

def main(tables_path, oracle_path, q):
    orc = {r["id"]: r for r in map(json.loads, open(oracle_path))}
    out = {"tables": 0, "skipped_unresolved": 0, "skipped_degenerate": 0, "not_closed": 0,
           "closed": 0, "rules_with_dec": 0, "hits": []}
    for line in open(tables_path):
        t = json.loads(line)
        out["tables"] += 1
        o = orc[t["id"]]
        if not o["resolved"]:
            out["skipped_unresolved"] += 1
            continue
        if not o["labels_distinct"]:
            out["skipped_degenerate"] += 1
            continue
        ns, nm = t["ns"], t["nm"]
        S = ["1"] + [f"s{i}" for i in range(1, ns)]
        M = ["1"] + [f"m{i}" for i in range(1, nm)]
        cells = [f"{s}|{m}" for s in S for m in M]
        given = uf_partition(cells, t["rels"], t["fwd"])
        realized = {frozenset(b) for b in o["fwd_classes"]}
        if given != realized:
            out["not_closed"] += 1
            continue
        out["closed"] += 1
        fblocks = sorted(sorted(b) for b in realized)
        fidx = {c: i for i, b in enumerate(fblocks) for c in b}
        rblocks = sorted(sorted(b) for b in o["rev_classes"])
        ridx = {c: i for i, b in enumerate(rblocks) for c in b}
        memtuples = list(itertools.product(range(q), repeat=nm))
        mem_pos = {w: i for i, w in enumerate(memtuples)}
        # forward: for each class assignment p, the memory tuple read by each relay
        fwd_rows = []
        for p in itertools.product(range(q), repeat=len(fblocks)):
            rows = tuple(mem_pos[tuple(p[fidx[f"{s}|{m}"]] for m in M)] for s in S)
            fwd_rows.append((rows, p[fidx["1|1"]]))
        # reverse: for each class assignment r, the relay-output tuple read at each m
        rev_rows = []
        for r in itertools.product(range(q), repeat=len(rblocks)):
            ztup = tuple(tuple(r[ridx[f"{m}|{s}"]] for s in S) for m in M)
            rev_rows.append((ztup, r[ridx["1|1"]]))
        for mu in itertools.product(range(q), repeat=len(memtuples)):
            forced = {}
            ok = True
            for rows, demand in fwd_rows:
                y = tuple(mu[i] for i in rows)
                prev = forced.get(y)
                if prev is None:
                    forced[y] = demand
                elif prev != demand:
                    ok = False
                    break
            if not ok:
                continue
            out["rules_with_dec"] += 1
            hit = None
            for ztup, demand in rev_rows:
                free = sorted({z for z in ztup if z not in forced})
                for vals in itertools.product(range(q), repeat=len(free)):
                    ext = dict(zip(free, vals))
                    outs = tuple(forced[z] if z in forced else ext[z] for z in ztup)
                    if mu[mem_pos[outs]] != demand:
                        hit = {"table": t["id"], "mu": list(mu), "q_reverse": list(ztup),
                               "free_values": {str(k): v for k, v in ext.items()}}
                        break
                if hit:
                    break
            if hit:
                out["hits"].append(hit)
    print(json.dumps({"input": tables_path, "q": q, **{k: (v if k != "hits" else len(v)) for k, v in out.items()}}))
    if out["hits"]:
        print(json.dumps(out["hits"][:20]))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]))
