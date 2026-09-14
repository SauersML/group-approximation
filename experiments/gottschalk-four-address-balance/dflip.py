#!/usr/bin/env python3
"""Perturbation refinement for surviving binary four-address rules.

State: a set R of relators in a, b, c (memory M = {1, a, b, c}).  G_R is the universal group.
A state is CLOSED when G_R is amenable or collapses the memory (every group realizing R has an
amenable memory group, or no group realizes R with four distinct memory elements).

For an open state we look for an invisible perturbation: flip the sites F = {1} or F = {1, g}
(g a short word), with values on the context sites chosen so that every output site reading F
sees the same rule value before and after.  The instance is computed exactly in G_R by normal
forms.  A solution stays valid in every group realizing R unless one of these merges happens:
  (i)   two context sites carrying different bits become equal;
  (ii)  a context site becomes equal to a flipped site;
  (iii) two output sites become equal.
Each such merge is one extra relator.  The groups where the solution fails are covered by the
extended states R + {relator}, which we decide and refine recursively.  A rule is EXCLUDED when
every branch closes; open leaves are reported with their relators.
"""
import itertools, json, sys
import analyze2 as A
import gp

MEMW = A.MEM


NF_CACHE = {}


def make_nf(rels):
    key = tuple(sorted(set(A.cyc_reduce(r) for r in rels) - {()}))
    if key not in NF_CACHE:
        NF_CACHE[key] = _make_nf(list(key))
    return NF_CACHE[key]


def _make_nf(rels):
    """Return (classification, nf) where nf maps a word to a canonical key in G_R, or
    (classification, None) when G_R is not recognized as a free product of cyclics."""
    gens, rels0, sub = A.eliminate([1, 2, 3], [A.cyc_reduce(r) for r in rels if A.cyc_reduce(r)],
                                   {1: (1,), 2: (2,), 3: (3,)})

    def levels():
        frontier = [(gens, rels0, sub)]
        yield frontier
        for depth in (1, 2):
            nxt = []
            for gs, rs, sb in frontier:
                for i, newword in A.nielsen_moves(gs):
                    a, b = newword
                    img = (i, -b) if a == i else (-a, i)
                    rs2 = sorted({A.cyc_reduce(A.subst(r, i, img)) for r in rs} - {()})
                    sb2 = {o: A.subst(w, i, img) for o, w in sb.items()}
                    nxt.append(A.eliminate(list(gs), rs2, sb2))
            yield nxt
            frontier = nxt[:300]

    for level in levels():
        res = _classify_level(level)
        if res is not None:
            return res
    return {"form": "undecided"}, None


def _classify_level(cands):
    for gs, rs, sb in cands:
        if not gs:
            return {"form": "trivial", "amenable": True, "memory_distinct": False}, None
        po, rest = A.power_normalize(gs, rs)
        if rest:
            cls, nf = gp.classify(gs, rs, sb)
            if cls is not None:
                return cls, nf
            continue
        orders = po
        nontriv = sorted(orders[g] for g in gs if orders[g] != 1)
        amen = len(nontriv) <= 1 or nontriv == [2, 2]

        def nf(w, orders=orders, sb=sb):
            return A.fp_normal(A.subst_all(w, sb), orders)

        mems = [nf(m) for m in MEMW]
        return {"form": "free-product-of-cyclics", "factors": nontriv, "amenable": amen,
                "memory_distinct": len(set(mems)) == 4}, nf
    return None


def rule_eval(mu, bits):
    x = bits[0] | (bits[1] << 1) | (bits[2] << 2) | (bits[3] << 3)
    return (mu >> x) & 1


def instance(mu, nf, g):
    """Build the perturbation instance for F = {1} (g None) or F = {1, g}."""
    one = nf(())
    flips = [()] if g is None else [(), g]
    fkeys = [nf(f) for f in flips]
    if len(set(fkeys)) != len(fkeys):
        return None
    outs = {}
    for f in flips:
        for m in MEMW:
            o = A.mul(f, A.inv(m))
            outs.setdefault(nf(o), o)
    rows = []   # per output: list of (kind, key) for coordinates 0..3
    words = {}  # key -> representative word
    for ko, o in outs.items():
        row = []
        for m in MEMW:
            s = A.mul(o, m)
            k = nf(s)
            words.setdefault(k, s)
            if k in fkeys:
                row.append(("F", fkeys.index(k)))
            else:
                row.append(("C", k))
        rows.append((ko, o, row))
    return {"flips": flips, "fkeys": fkeys, "rows": rows, "words": words, "outs": outs}


def solve(mu, inst, limit=200):
    """Enumerate up to `limit` invisible assignments (dict var -> bit, vars ('F',i) or ('C',key))."""
    rows = inst["rows"]
    sols = []
    assign = {}

    def rec(r):
        if len(sols) >= limit:
            return
        if r == len(rows):
            sols.append(dict(assign))
            return
        _, _, row = rows[r]
        vars_ = list(dict.fromkeys(row))
        for vals in itertools.product((0, 1), repeat=len(vars_)):
            loc = dict(zip(vars_, vals))
            if any(v in assign and assign[v] != loc[v] for v in vars_):
                continue
            before = [loc[v] for v in row]
            after = [(1 - loc[v]) if v[0] == "F" else loc[v] for v in row]
            if rule_eval(mu, before) != rule_eval(mu, after):
                continue
            newly = [v for v in vars_ if v not in assign]
            for v in newly:
                assign[v] = loc[v]
            rec(r + 1)
            for v in newly:
                del assign[v]

    rec(0)
    return sols


def conflicts(inst, sol):
    words = inst["words"]
    flipw = inst["flips"]
    ctx = [(k, b) for (kind, k), b in sol.items() if kind == "C"]
    rels = set()
    for (k1, b1), (k2, b2) in itertools.combinations(ctx, 2):
        if b1 != b2:
            rels.add(A.cyc_reduce(A.mul(A.inv(words[k1]), words[k2])))
    for k, _ in ctx:
        for f in flipw:
            rels.add(A.cyc_reduce(A.mul(A.inv(words[k]), f)))
    outw = list(inst["outs"].values())
    for o1, o2 in itertools.combinations(outw, 2):
        rels.add(A.cyc_reduce(A.mul(A.inv(o1), o2)))
    rels.discard(())
    return sorted(rels)


def short_words():
    qs = {A.quotient(i, j) for (i, j) in A.PAIRS}
    ws = set(qs)
    for q1 in qs:
        for q2 in qs:
            w = A.mul(q1, q2)
            if w:
                ws.add(w)
    return sorted(ws, key=lambda w: (len(w), w))


SHORT = short_words()
MEMO = {}
STATS = {"states": 0}


def key_of(rels):
    return tuple(sorted(set(A.cyc_reduce(r) for r in rels) - {()}))


def refine(mu, rels, depth, max_depth, budget):
    k = (mu, key_of(rels))
    if k in MEMO:
        return MEMO[k]
    STATS["states"] += 1
    if STATS["states"] > budget:
        return {"status": "budget", "relators": [list(r) for r in key_of(rels)]}
    cls, nf = make_nf(list(key_of(rels)))
    if cls.get("memory_distinct") is False:
        res = {"status": "closed", "why": "memory-collapse"}
    elif cls.get("amenable") is True:
        res = {"status": "closed", "why": "amenable", "form": cls}
    elif nf is None:
        res = {"status": "open", "why": "undecided-group", "relators": [list(r) for r in key_of(rels)]}
    elif depth >= max_depth:
        res = {"status": "open", "why": "depth", "form": cls, "relators": [list(r) for r in key_of(rels)]}
    else:
        best = None
        for g in [None] + SHORT[:60]:
            inst = instance(mu, nf, g)
            if inst is None:
                continue
            sols = solve(mu, inst)

            def cheap(sol):
                bits = [b for (kind, _), b in sol.items() if kind == "C"]
                return bits.count(0) * bits.count(1)

            sols = sorted(sols, key=cheap)[:3]
            for sol in sols:
                cf = conflicts(inst, sol)
                # quick score: conflicts whose extended group is not immediately closed
                score = 0
                pending = []
                for r in cf:
                    c2, _ = make_nf(list(key_of(rels)) + [r])
                    if not (c2.get("memory_distinct") is False or c2.get("amenable") is True):
                        score += 1
                        pending.append(r)
                if best is None or score < best[0]:
                    best = (score, g, sol, pending)
                if score == 0:
                    break
            if best is not None and best[0] == 0:
                break
        if best is None:
            res = {"status": "open", "why": "no-perturbation", "form": cls,
                   "relators": [list(r) for r in key_of(rels)]}
        else:
            score, g, sol, pending = best
            children = {}
            ok = True
            for r in pending:
                ch = refine(mu, list(key_of(rels)) + [r], depth + 1, max_depth, budget)
                children[json.dumps(list(r))] = ch
                if ch["status"] != "closed":
                    ok = False
            res = {"status": "closed" if ok else "open", "why": "perturbation",
                   "flip": None if g is None else list(g),
                   "n_pending": score, "children": children}
            if not ok:
                res["relators"] = [list(r) for r in key_of(rels)]
    MEMO[k] = res
    return res


def main():
    tri = json.load(open(sys.argv[1]))
    flip = json.load(open(sys.argv[2]))
    max_depth = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    budget = int(sys.argv[4]) if len(sys.argv) > 4 else 20000
    parts = [tuple(p) for p in flip["partitions"]]
    out = {}
    closed = []
    for mu_s, bad in sorted(tri["survivors"].items(), key=lambda kv: int(kv[0])):
        mu = int(mu_s)
        branches = {}
        allc = True
        for k in bad:
            rels = A.relators(parts[int(k)])
            res = refine(mu, rels, 0, max_depth, budget)
            branches[str(k)] = res
            if res["status"] != "closed":
                allc = False
        out[mu_s] = {"closed": allc, "branches": branches}
        if allc:
            closed.append(mu)
        sys.stderr.write("rule %s closed=%s states=%d\n" % (mu_s, allc, STATS["states"]))
    summary = {"survivors_in": len(tri["survivors"]), "closed_now": len(closed),
               "still_open": len(tri["survivors"]) - len(closed), "states": STATS["states"],
               "max_depth": max_depth, "budget": budget}
    json.dump({"summary": summary, "closed": closed, "rules": out}, sys.stdout)
    sys.stderr.write(json.dumps(summary) + "\n")


if __name__ == "__main__":
    main()
