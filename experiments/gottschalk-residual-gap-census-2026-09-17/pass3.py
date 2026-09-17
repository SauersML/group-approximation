#!/usr/bin/env python3
"""Third pass on CANDIDATE records of pass2.py: Tietze-eliminate generators, then low-index subgroups of higher degree.

Every relator of P(T) in which some generator occurs exactly once is solved for that generator, which is then
substituted everywhere (a Tietze move, so the group is unchanged). Sims1 then runs on the smaller presentation
up to degree NMAX. Each representation is pulled back to permutations of the ORIGINAL generators through the
substitution words, and verify.py checks those against the original relators.

Usage: pass3.py ns nm in.jsonl out.jsonl NMAX SIMSSEC
"""
import itertools
import json
import sys
import time

from libsemigroups_pybind11 import Presentation, ReportGuard, Sims1, presentation

from gapcensus import active_nodes

RG = ReportGuard(False)


def inv(w):
    return [-x for x in reversed(w)]


def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def cyc_reduce(w):
    w = free_reduce(w)
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return w


def tietze(ngen, relators):
    """Generators 1..ngen. Returns (defs, remaining generators, relators) with defs[g] a word in remaining gens."""
    defs = {g: [g] for g in range(1, ngen + 1)}
    rels = [cyc_reduce(r) for r in relators]
    rels = [r for r in rels if r]
    changed = True
    while changed:
        changed = False
        for r in rels:
            counts = {}
            for x in r:
                counts[abs(x)] = counts.get(abs(x), 0) + 1
            cand = [g for g, c in counts.items() if c == 1]
            if not cand:
                continue
            g = cand[0]
            i = [k for k, x in enumerate(r) if abs(x) == g][0]
            rot = r[i:] + r[:i]  # rot = g^e * rest = 1
            e = rot[0]
            rest = rot[1:]
            val = inv(rest) if e > 0 else rest  # g = rest^-1 or g^-1 = rest

            def sub(w):
                out = []
                for x in w:
                    if x == g:
                        out += val
                    elif x == -g:
                        out += inv(val)
                    else:
                        out.append(x)
                return free_reduce(out)
            for h in defs:
                defs[h] = sub(defs[h])
            rels = [cyc_reduce(sub(q)) for q in rels if q is not r]
            rels = [q for q in rels if q]
            changed = True
            break
    remaining = sorted({abs(x) for h in defs for x in defs[h]})
    return defs, remaining, rels


def main():
    ns, nm, fin, fout = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    NMAX, simssec = int(sys.argv[5]), float(sys.argv[6])
    stats = {}
    with open(fin) as fi, open(fout, "w") as fh:
        for line in fi:
            r = json.loads(line)
            if r["status"] != "CANDIDATE":
                continue
            ng = ns - 1 + nm - 1
            relators = []
            for (u, v) in r["rels"]:
                relators.append([a // 2 + 1 for a in u] + inv([a // 2 + 1 for a in v]))
            defs, rem, rels = tietze(ng, relators)
            idx = {g: k for k, g in enumerate(rem)}
            p = Presentation(list(range(2 * len(rem))))
            p.contains_empty_word(True)
            invl = []
            for k in range(len(rem)):
                invl += [2 * k + 1, 2 * k]
            presentation.add_inverse_rules(p, invl)

            def letters(w):
                return [2 * idx[abs(x)] + (0 if x > 0 else 1) for x in w]
            for q in rels:
                presentation.add_rule(p, letters(q), [])

            def ls(s):
                return [] if s == 0 else [s]

            def lm(m):
                return [] if m == 0 else [ns - 1 + m]
            rcl = r["rev_classes"]
            words = [free_reduce([y for x in lm(c[0][0]) + ls(c[0][1]) for y in defs[x]]) for c in rcl]
            pairs = {(i, j) for i, j in itertools.combinations(range(len(rcl)), 2)}
            # only the pairs pass2 left unseparated need new witnesses
            unsep = {tuple(map(tuple, pr)) for pr in [tuple(tuple(x) for x in pr) for pr in r["unseparated"]]}
            rep_index = {tuple(c[0]): i for i, c in enumerate(rcl)}
            pairs = set()
            for a, b in r["unseparated"]:
                i, j = rep_index[tuple(a)], rep_index[tuple(b)]
                pairs.add((min(i, j), max(i, j)))
            witnesses = list(r["witnesses"])
            t0 = time.time()
            for wg in Sims1(p).iterator(NMAX):
                nn = active_nodes(wg, 2 * len(rem))

                def perm(w):
                    pts = list(range(nn))
                    for x in letters(w):
                        pts = [wg.target(y, x) for y in pts]
                    return tuple(pts)
                perms = [perm(w) for w in words]
                sep = {(i, j) for (i, j) in pairs if perms[i] != perms[j]}
                if sep:
                    gens = [perm(defs[g]) for g in range(1, ng + 1)]
                    witnesses.append({"degree": nn, "gens": gens, "separates": len(sep), "family": "tietze-sims"})
                    pairs -= sep
                if not pairs or time.time() - t0 > simssec:
                    break
            rec = dict(r)
            rec["witnesses"] = witnesses
            rec["tietze"] = {"remaining": len(rem), "relators": rels}
            if pairs:
                rec["status"] = "CANDIDATE"
                rec["unseparated"] = [[rcl[i][0], rcl[j][0]] for (i, j) in sorted(pairs)]
            else:
                rec["status"] = "RESOLVED"
                rec.pop("unseparated", None)
            stats[rec["status"]] = stats.get(rec["status"], 0) + 1
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            print(r["id"], rec["status"], len(rem), rels, "%.1fs" % (time.time() - t0), flush=True)
    print("pass3", stats, flush=True)


if __name__ == "__main__":
    main()
