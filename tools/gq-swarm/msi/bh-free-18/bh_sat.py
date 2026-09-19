#!/usr/bin/env python3
"""Lazy SAT (counterexample-guided) decision of the free rules of binary_hier.py (lane bh-free-18).

Variables: the 15 free positions (R, input) of the fill, each taking one of the 5 free outputs, all different for
each neighbour value R, so 120^3 = 1,728,000 fills.
Clauses: nogoods. A nogood is the set of fill facts (R, input, output) consulted by one failing certificate
computation. The computation is deterministic given those facts, so it fails for EVERY fill containing them.
Search: one DFS over the fill tree. Every assignment is checked against the clauses indexed by its fact, and clauses
added later are rechecked against the prefix whenever a level resumes, which gives backjumping. At each full fill
that survives, the certificate runs. On failure, the subset-minimal nogoods of ALL failing configurations of the
first failing check are added. The search is complete: it ends with a passing fill (SAT) or an exhausted tree (UNSAT).

Modes:
  planted  P with the uncorrected A (fails independently of the fill): must be UNSAT at once;
  orbit    calibration on hierarchical tapes: tower and phi U^2 = U phi at A-points of the zero-tape orbits: SAT;
  full     the renormalization criterion R, T, C2, P, P-1, I (bh_run.CHECKS2), returns capped at 40.
Usage: python3 bh_sat.py MODE NPROC SECONDS
"""
import sys
import time
import subprocess
from math import factorial
from collections import defaultdict
from multiprocessing import Pool
import binary_hier as B
import bh_run as H
import bh_lazy as L
import bh_cbj as C          # patches B.matching / B.Finv to log consulted fill facts in C.LOG

VARS = [(R, key) for R in range(3) for key in L.FILL_KEYS[R]]
OUTS = list(B.FILL_OUT)
ORDER = list(OUTS)          # value order of the DFS; reversed in orbit mode so the default fill comes LAST
MODE = None


def inA_old(cfg, asg):
    if cfg.ph != 2:
        return False
    s, h = cfg.s, cfg.h
    if s == "A>":
        c, n = B.val(cfg, h, asg), B.val(cfg, h + 1, asg)
        return c != 0 and (n == 0 or c == 2)
    if s == "A<":
        c, n = B.val(cfg, h, asg), B.val(cfg, h - 1, asg)
        return c != 0 and (n == 0 or c == 2)
    return False


def exhaust_fail(M, checks):
    """First failing check: (name, number of failing configurations, set of nogoods), or None."""
    for name, sts, mk in checks:
        body = mk(M)
        ngs = set()
        nf = 0
        for (s, ph) in sts:
            stack = [{}]
            while stack:
                asg = stack.pop()
                C.LOG.clear()
                try:
                    ok = body(s, ph, asg)
                except B.Need as e:
                    for c in range(3):
                        a2 = dict(asg)
                        a2[e.k] = c
                        stack.append(a2)
                    continue
                except B.Fail as e:
                    ok = str(e)
                if ok is not True and ok is not None:
                    nf += 1
                    ngs.add(frozenset(C.LOG))
        if nf:
            return name, nf, ngs
    return None


def orbit_fail(M, steps=3000):
    H.L = 2001
    ngs = set()
    for q in ["A>", "A<", "P>", "P<", "X>", "X<", "S>", "S<"]:
        C.LOG.clear()
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
                ngs.add(frozenset(C.LOG))
                break
    return ("orbit", len(ngs), ngs) if ngs else None


def evaluate(assign):
    M = L.make(assign)
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
ST = {"elim": 0, "leaves": 0}


def add_clause(ng):
    CL.append(ng)
    for f in ng:
        IDX[f].append(ng)


def holds(cl, assign):
    return all(assign.get((R, k)) == o for (R, k, o) in cl)


def completions(assign):
    p = 1
    for R in range(3):
        p *= factorial(5 - sum(1 for (RR, _) in assign if RR == R))
    return p


def gen(depth, assign, used):
    if depth == len(VARS):
        yield dict(assign)
        return
    R, key = VARS[depth]
    seen = len(CL)
    free = [o for o in ORDER if o not in used[R]]
    for i, o in enumerate(free):
        assign[(R, key)] = o
        used[R].add(o)
        if any(holds(c, assign) for c in IDX[(R, key, o)]):
            ST["elim"] += completions(assign)
        else:
            yield from gen(depth + 1, assign, used)
        del assign[(R, key)]
        used[R].discard(o)
        new = CL[seen:]
        seen = len(CL)
        if any(holds(c, assign) for c in new):
            for o2 in free[i + 1:]:
                assign[(R, key)] = o2
                ST["elim"] += completions(assign)
                del assign[(R, key)]
            return


def digits(assign):
    return "".join(str(OUTS.index(assign[(R, k)])) for R in range(3) for k in L.FILL_KEYS[R])


def spot_check(pool, k=10):
    """Soundness of nogoods: a random completion of a learned nogood must fail again."""
    import random
    rnd = random.Random(7)
    tests = []
    for ng in CL[:k]:
        a = {(R, key): o for (R, key, o) in ng}
        for R in range(3):
            rest = [o for o in OUTS if o not in {a[x] for x in a if x[0] == R}]
            rnd.shuffle(rest)
            for key in L.FILL_KEYS[R]:
                if (R, key) not in a:
                    a[(R, key)] = rest.pop()
        tests.append(a)
    res = pool.map(evaluate, tests)
    bad = sum(1 for _, r in res if r is None)
    print("  spot-check: %d random completions of learned nogoods, %d did NOT fail (must be 0)" % (len(res), bad), flush=True)


def main(mode, nproc, budget):
    global MODE, ORDER
    MODE = mode
    if mode == "orbit":
        ORDER = OUTS[::-1]
    checked = False
    t0 = time.time()
    g = gen(0, {}, {0: set(), 1: set(), 2: set()})
    sizes = defaultdict(int)
    verdict = None
    last = 0
    with Pool(nproc) as pool:
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
                    print("SAT fill", digits(assign), sorted(assign.items()), flush=True)
                    break
                name, nf, kept = r
                ST["elim"] += 1
                for ng in kept:
                    sizes[len(ng)] += 1
                    add_clause(ng)
                if frozenset() in kept:
                    verdict = "UNSAT"
                    print("empty nogood from check", name, flush=True)
                    break
            if mode == "full" and not checked and len(CL) >= 10:
                checked = True
                spot_check(pool)
            if time.time() - last > 30:
                last = time.time()
                print("  %s leaves=%d clauses=%d eliminated=%d/1728000 sizes=%s %.0fs" % (
                    mode, ST["leaves"], len(CL), ST["elim"], dict(sorted(sizes.items())), time.time() - t0), flush=True)
    print("VERDICT %s mode=%s leaves=%d clauses=%d eliminated=%d/1728000 sizes=%s %.0fs" % (
        verdict, mode, ST["leaves"], len(CL), ST["elim"], dict(sorted(sizes.items())), time.time() - t0), flush=True)
    small = sorted(CL, key=len)[:8]
    for ng in small:
        print("  smallest nogood", len(ng), sorted(ng))
    if verdict == "SAT" and mode == "full":
        print(subprocess.run([sys.executable, "bh_run.py", "cert2", digits(assign)], capture_output=True, text=True).stdout)


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]), float(sys.argv[3]))
