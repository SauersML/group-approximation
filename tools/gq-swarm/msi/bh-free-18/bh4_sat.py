#!/usr/bin/env python3
"""The binary hierarchy machine with a fourth letter c = 3 (a marker), decided by lazy SAT (lane bh-free-18).

The 10 fixed rules per neighbour value of binary_hier.py are kept, and c counts as nonzero (so ('T<',0) is fixed
for neighbour c, while ('S>',2) is free there). Every rule that reads c, or whose neighbour is c, is free. For each
neighbour value R in {0,a,b,c}, the '>'-reading group then has 10 free inputs:
  - the 5 old free inputs;
  - (A>,c), (P>,c), (X<,c), (T<,c), (S>,c).
They map bijectively onto 10 free outputs:
  - the 5 old free outputs;
  - (c,P>), (c,X<), (c,T<), (c,S<), (c,A<).
The mirror group is the mirror image. This is the most general marker the rule format allows: any placement of c
by the machine, including "write c on a b-run", is some fill.
Y, A and phi are those of binary_hier.py, with c nonzero. The checks are bh_run.CHECKS2 (R, T, C2, P, P-1, I),
returns capped at 40, and the unread cells range over 4 letters.
Clauses and search are as in bh_sat.py.
Modes: planted (P with the uncorrected A: UNSAT at once), orbit (zero-tape orbits: SAT), full.
Usage: python3 bh4_sat.py MODE NPROC SECONDS
"""
import sys
import time
from math import factorial
from collections import defaultdict
from multiprocessing import Pool
import binary_hier as B
import bh_run as H

NL = 4
LOG = set()
MIRS = B.mir_state


def resolve(inp, R):
    if inp == "U":
        return ("T<", 0) if R == 0 else ("S>", 2)
    return inp


FKEYS = {R: [resolve(i, R) for i in B.FILL_IN] + [("A>", 3), ("P>", 3), ("X<", 3), ("T<", 3), ("S>", 3)]
         for R in range(NL)}
FOUTS = list(B.FILL_OUT) + [(3, "P>"), (3, "X<"), (3, "T<"), (3, "S<"), (3, "A<")]
NF = len(FOUTS)
SPEC_OUT = set(B.SPEC_R.values()) | {(0, "S<")}
OUT_R = SPEC_OUT | set(FOUTS)
assert len(OUT_R) == 20 and not (SPEC_OUT & set(FOUTS))
VARS = [(R, k) for R in range(NL) for k in FKEYS[R]]


def make(assign):
    tab = {}
    for R in range(NL):
        t = dict(B.SPEC_R)
        if R != 0:
            t[("T<", 0)] = (0, "S<")
        else:
            t[("S>", 2)] = (0, "S<")
        for (RR, key), out in assign.items():
            if RR == R:
                t[key] = out
        tab[R] = t
    inv = {R: {v: k for k, v in tab[R].items()} for R in range(NL)}
    return {"tab": tab, "inv": (OUT_R, inv)}


def matching(tab, q, cfg, asg):
    c = B.val(cfg, cfg.h, asg)
    grp = q in B.GROUP_R
    key = (q if grp else MIRS(q), c)
    n = B.val(cfg, cfg.h + 1 if grp else cfg.h - 1, asg)
    w, s = tab[n][key]
    if key in FKEYS[n]:
        LOG.add((n, key, (w, s)))
    return (w, s) if grp else (w, MIRS(s))


def Finv(tab, invd, cfg, asg):
    outR, inv = invd
    if cfg.ph == 1:
        cfg.h -= B.DIR[cfg.s[1]]
        cfg.ph = 2
        return
    s, c = cfg.s, B.val(cfg, cfg.h, asg)
    if (c, s) in outR:
        n, o, mirror = B.val(cfg, cfg.h + 1, asg), (c, s), False
    else:
        n, o, mirror = B.val(cfg, cfg.h - 1, asg), (c, MIRS(s)), True
    q, a = inv[n][o]
    if o in FOUTS:
        LOG.add((n, (q, a), o))
    cfg.t[cfg.h] = a
    cfg.s, cfg.ph = (MIRS(q) if mirror else q), 1


B.matching = matching
B.Finv = Finv
MODE = None


def inA_old(cfg, asg):
    if cfg.ph != 2 or cfg.s[0] != "A":
        return False
    d = 1 if cfg.s == "A>" else -1
    c, n = B.val(cfg, cfg.h, asg), B.val(cfg, cfg.h + d, asg)
    return c != 0 and (n == 0 or c == 2)


def exhaust_fail(M, checks):
    for name, sts, mk in checks:
        body = mk(M)
        ngs = set()
        nf = 0
        for (s, ph) in sts:
            stack = [{}]
            while stack:
                asg = stack.pop()
                LOG.clear()
                try:
                    ok = body(s, ph, asg)
                except B.Need as e:
                    for c in range(NL):
                        a2 = dict(asg)
                        a2[e.k] = c
                        stack.append(a2)
                    continue
                except B.Fail as e:
                    ok = str(e)
                if ok is not True and ok is not None:
                    nf += 1
                    ngs.add(frozenset(LOG))
                    if nf >= 300:
                        return name, nf, ngs
        if nf:
            return name, nf, ngs
    return None


def orbit_fail(M, steps=3000):
    H.L = 2001
    for q in ["A>", "A<", "P>", "P<", "X>", "X<", "S>", "S<"]:
        LOG.clear()
        c = H.zero_cfg(q)
        for n in range(steps):
            try:
                B.F(M["tab"], c, {})
                if B.inY(c, {}) and B.inA(c, {}):
                    lhs = c.copy()
                    B.U(M, lhs, {})
                    if B.inA(lhs, {}):
                        raise B.Fail("U y in A")
                    B.U(M, lhs, {})
                    if not B.inA(lhs, {}):
                        raise B.Fail("U^2 y not in A")
                    B.phi(lhs, {})
                    rhs = c.copy()
                    B.phi(rhs, {})
                    B.U(M, rhs, {})
                    if not B.same(lhs, rhs, {}):
                        raise B.Fail("identity")
            except B.Fail:
                return ("orbit", 1, {frozenset(LOG)})
    return None


def evaluate(assign):
    M = make(assign)
    if MODE == "planted":
        B.inA = inA_old
        r = exhaust_fail(M, [("P-old", B.PH2, B.body_phi)])
    elif MODE == "orbit":
        r = orbit_fail(M)
    else:
        r = exhaust_fail(M, H.CHECKS2)
    if r is None:
        return assign, None
    name, nf, ngs = r
    kept = []
    for ng in sorted(ngs, key=len):
        if not any(k <= ng for k in kept):
            kept.append(ng)
            if len(kept) >= 400:
                break
    return assign, (name, nf, kept)


CL = []
IDX = defaultdict(list)
ST = {"leaves": 0}


def holds(cl, assign):
    return all(assign.get((R, k)) == o for (R, k, o) in cl)


def gen(depth, assign, used, order):
    if depth == len(VARS):
        yield dict(assign)
        return
    R, key = VARS[depth]
    seen = len(CL)
    free = [o for o in order if o not in used[R]]
    for o in free:
        assign[(R, key)] = o
        used[R].add(o)
        if not any(holds(c, assign) for c in IDX[(R, key, o)]):
            yield from gen(depth + 1, assign, used, order)
        del assign[(R, key)]
        used[R].discard(o)
        new = CL[seen:]
        seen = len(CL)
        if any(holds(c, assign) for c in new):
            return


def spot_check(pool, clauses, label):
    import random
    rnd = random.Random(7)
    tests = []
    for ng in clauses:
        a = {(R, key): o for (R, key, o) in ng}
        for R in range(NL):
            rest = [o for o in FOUTS if o not in {a[x] for x in a if x[0] == R}]
            rnd.shuffle(rest)
            for key in FKEYS[R]:
                if (R, key) not in a:
                    a[(R, key)] = rest.pop()
        tests.append(a)
    res = pool.map(evaluate, tests)
    print("  spot-check (%s): %d random 4-letter completions of nogoods, %d did NOT fail (must be 0)"
          % (label, len(res), sum(1 for _, r in res if r is None)), flush=True)


def main(mode, nproc, budget):
    global MODE
    MODE = mode
    if mode == "full":
        import os
        import pickle
        if os.path.exists("clauses3.pkl"):
            seeds = pickle.load(open("clauses3.pkl", "rb"))
            for ng in seeds:
                CL.append(ng)
                for f in ng:
                    IDX[f].append(ng)
            print("seeded %d clauses from the 3-letter search (they transfer: c-free tapes, same rules)" % len(seeds), flush=True)
    NSEED = len(CL)
    order = FOUTS[::-1] if mode == "orbit" else FOUTS
    t0 = time.time()
    g = gen(0, {}, {R: set() for R in range(NL)}, order)
    sizes = defaultdict(int)
    verdict = None
    last = 0
    checked = False
    with Pool(nproc) as pool:
        if mode == "full" and NSEED:
            spot_check(pool, sorted(CL, key=len)[:4] + CL[-2:], "transferred 3-letter seeds")
        while verdict is None:
            if time.time() - t0 > budget:
                verdict = "TIMEOUT"
                break
            batch = []
            for a in g:
                batch.append(a)
                if len(batch) >= nproc:
                    break
            if not batch:
                verdict = "UNSAT"
                break
            for assign, r in pool.map(evaluate, batch):
                ST["leaves"] += 1
                if r is None:
                    verdict = "SAT"
                    print("SAT fill", sorted(assign.items()), flush=True)
                    break
                name, nf, kept = r
                for ng in kept:
                    sizes[len(ng)] += 1
                    CL.append(ng)
                    for f in ng:
                        IDX[f].append(ng)
                if frozenset() in kept:
                    verdict = "UNSAT"
                    print("empty nogood from check", name, flush=True)
                    break
            if mode == "full" and not checked and len(CL) >= NSEED + 8:
                checked = True
                spot_check(pool, CL[-8:], "learned")
            if time.time() - last > 30:
                last = time.time()
                print("  %s leaves=%d clauses=%d sizes=%s %.0fs" % (mode, ST["leaves"], len(CL),
                      dict(sorted(sizes.items())), time.time() - t0), flush=True)
    print("VERDICT %s mode=%s leaves=%d clauses=%d sizes=%s %.0fs" % (verdict, mode, ST["leaves"], len(CL),
          dict(sorted(sizes.items())), time.time() - t0), flush=True)
    for ng in sorted(CL, key=len)[:10]:
        print("  smallest nogood", len(ng), sorted(ng))


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), float(sys.argv[3]))
