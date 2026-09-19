#!/usr/bin/env python3
"""Unfrozen binary hierarchy machine: fix only the rules the hierarchy uses, decide the rest by SAT (lane bh-free-18).

1. HIERARCHY. Run the design machine (binary_hier.py, default fill) on zero tapes from its 8 non-T states and record
   every (neighbour value, reading input) context F consults, in '>'-group coordinates. Those rules stay fixed.
2. FREE. Every other context is free. For each neighbour value n, the free inputs map bijectively onto the outputs
   the design gives them, so the machine stays reversible with a local inverse.
3. SAT. Boolean x[n,input,output] with exactly-one constraints both ways. A master solver (z3 if importable, else a
   DFS with clause index) proposes fills. Each fill runs the local certificate bh_run.CHECKS2 (R, T, C2, P, P-1, I;
   returns capped at 40). Every failing configuration adds the nogood "not all of the free facts it consulted", which
   holds for every fill containing those facts. UNSAT is a proof over the whole unfrozen space. SAT gives a fill
   passing the certificate.
Calibrations: planted (P with the uncorrected A: UNSAT at once); pinned (the old fixed rules pinned to the design:
must reproduce job 1327013's UNSAT); soundness (random completions of learned nogoods fail again); the orbits of the
first fill consult no free rule.
Usage: python3 bh_unfreeze.py NPROC PINNED_SECONDS MAIN_SECONDS
"""
import sys
import time
import random
from collections import defaultdict
from multiprocessing import Pool
import binary_hier as B
import bh_run as H

DESIGN = B.build(B.DEFAULT)                  # neighbour value -> {input: output}, the design with the default fill
NL = 3
OUTR = set(DESIGN[0].values())
assert all(set(DESIGN[n].values()) == OUTR for n in range(NL)) and len(OUTR) == 15
OLD_FREE = {n: set(B.FILL_IN[:4]) | {("T<", 0) if n == 0 else ("S>", 2)} for n in range(NL)}
LOG = set()
CTX = set()
FREE = {}
FOUT = {}
MODE = "main"


def matching(tab, q, cfg, asg):
    c = B.val(cfg, cfg.h, asg)
    grp = q in B.GROUP_R
    key = (q if grp else B.mir_state(q), c)
    n = B.val(cfg, cfg.h + 1 if grp else cfg.h - 1, asg)
    w, s = tab[n][key]
    CTX.add((n, key))
    if key in FREE.get(n, ()):
        LOG.add((n, key, (w, s)))
    return (w, s) if grp else (w, B.mir_state(s))


def Finv(tab, invd, cfg, asg):
    inv = invd
    if cfg.ph == 1:
        cfg.h -= B.DIR[cfg.s[1]]
        cfg.ph = 2
        return
    s, c = cfg.s, B.val(cfg, cfg.h, asg)
    if (c, s) in OUTR:
        n, o, mirror = B.val(cfg, cfg.h + 1, asg), (c, s), False
    else:
        n, o, mirror = B.val(cfg, cfg.h - 1, asg), (c, B.mir_state(s)), True
    q, a = inv[n][o]
    if o in FOUT.get(n, ()):
        LOG.add((n, (q, a), o))
    cfg.t[cfg.h] = a
    cfg.s, cfg.ph = (B.mir_state(q) if mirror else q), 1


B.matching = matching
B.Finv = Finv


def make(assign):
    tab = {n: dict(DESIGN[n]) for n in range(NL)}
    for (n, key), out in assign.items():
        tab[n][key] = out
    inv = {n: {v: k for k, v in tab[n].items()} for n in range(NL)}
    return {"tab": tab, "inv": inv}


def hierarchy_contexts(steps):
    H.L = 4001
    M = make({})
    CTX.clear()
    for q in ["A>", "A<", "P>", "P<", "X>", "X<", "S>", "S<"]:
        c = H.zero_cfg(q)
        for _ in range(steps):
            B.F(M["tab"], c, {})
    return set(CTX)


def inA_old(cfg, asg):
    if cfg.ph != 2 or cfg.s[0] != "A":
        return False
    d = 1 if cfg.s == "A>" else -1
    c, n = B.val(cfg, cfg.h, asg), B.val(cfg, cfg.h + d, asg)
    return c != 0 and (n == 0 or c == 2)


def exhaust_fail(M, checks, cap=3000):
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
                    for v in range(NL):
                        a2 = dict(asg)
                        a2[e.k] = v
                        stack.append(a2)
                    continue
                except B.Fail as e:
                    ok = str(e)
                if ok is not True and ok is not None:
                    nf += 1
                    ngs.add(frozenset(LOG))
                    if nf >= cap:
                        return name, nf, ngs
        if nf:
            return name, nf, ngs
    return None


def orbit_consults_free(M, steps=3000):
    H.L = 2001
    LOG.clear()
    for q in ["A>", "A<", "P>", "P<", "X>", "X<", "S>", "S<"]:
        c = H.zero_cfg(q)
        for _ in range(steps):
            B.F(M["tab"], c, {})
    return len(LOG)


def evaluate(assign):
    M = make(assign)
    if MODE == "planted":
        B.inA = inA_old
        r = exhaust_fail(M, [("P-old", B.PH2, B.body_phi)])
    else:
        r = exhaust_fail(M, H.CHECKS2)
    if r is None:
        return assign, None
    name, nf, ngs = r
    kept = []
    for ng in sorted(ngs, key=len):
        if not any(k <= ng for k in kept):
            kept.append(ng)
            if len(kept) >= 500:
                break
    return assign, (name, nf, kept)


class Master:
    """Exactly-one bijections per neighbour value plus nogood clauses; z3 if available, else DFS."""

    def __init__(self, pins):
        self.facts = [(n, k, o) for n in range(NL) for k in FREE[n] for o in FOUT[n]]
        self.kind = "dfs"
        try:
            sys.path.append("/projects/standard/hsiehph/sauer354/.local/lib/python3.10/site-packages")
            import z3
            self.z3 = z3
            self.v = {f: z3.Bool("x_%d_%s_%d_%d_%s" % (f[0], f[1][0], f[1][1], f[2][0], f[2][1])) for f in self.facts}
            self.s = z3.Solver()
            for n in range(NL):
                for k in FREE[n]:
                    row = [self.v[(n, k, o)] for o in FOUT[n]]
                    self.s.add(z3.PbEq([(x, 1) for x in row], 1))
                for o in FOUT[n]:
                    col = [self.v[(n, k, o)] for k in FREE[n]]
                    self.s.add(z3.PbEq([(x, 1) for x in col], 1))
            for f in pins:
                self.s.add(self.v[f])
            self.kind = "z3"
        except Exception as e:
            print("z3 unavailable (%r): DFS master" % (e,), flush=True)
            self.pins = {(n, k): o for (n, k, o) in pins}
            self.cl = []
            self.idx = defaultdict(list)
            self.vars = [(n, k) for n in range(NL) for k in FREE[n]]
            self.g = self._gen(0, {}, {n: set() for n in range(NL)})

    def add(self, ng):
        if self.kind == "z3":
            lits = [self.z3.Not(self.v[f]) for f in ng]
            if not lits:
                self.s.add(self.z3.BoolVal(False))
            elif len(lits) == 1:
                self.s.add(lits[0])
            else:
                self.s.add(self.z3.Or(lits))
        else:
            self.cl.append(ng)
            for f in ng:
                self.idx[f].append(ng)

    def _holds(self, c, a):
        return all(a.get((n, k)) == o for (n, k, o) in c)

    def _gen(self, d, a, used):
        if d == len(self.vars):
            yield dict(a)
            return
        n, k = self.vars[d]
        seen = len(self.cl)
        for o in ([self.pins[(n, k)]] if (n, k) in self.pins else FOUT[n]):
            if o in used[n]:
                continue
            a[(n, k)] = o
            used[n].add(o)
            if not any(self._holds(c, a) for c in self.idx[(n, k, o)]):
                yield from self._gen(d + 1, a, used)
            del a[(n, k)]
            used[n].discard(o)
            new = self.cl[seen:]
            seen = len(self.cl)
            if any(self._holds(c, a) for c in new):
                return

    def models(self, m):
        out = []
        if self.kind == "z3":
            for _ in range(m):
                if self.s.check() != self.z3.sat:
                    break
                mod = self.s.model()
                a = {(n, k): o for (n, k, o) in self.facts if self.z3.is_true(mod.eval(self.v[(n, k, o)], model_completion=True))}
                out.append(a)
                blk = [self.z3.Not(self.v[(n, k, o)]) for (n, k), o in a.items()]
                if not blk:
                    break
                self.s.add(blk[0] if len(blk) == 1 else self.z3.Or(blk))
        else:
            for a in self.g:
                out.append(a)
                if len(out) >= m:
                    break
        return out


def solve(label, pins, nproc, budget, pool):
    t0 = time.time()
    ms = Master(pins)
    clauses = []
    sizes = defaultdict(int)
    leaves = 0
    verdict = None
    checked = False
    last = time.time()
    while verdict is None:
        if time.time() - t0 > budget:
            verdict = "TIMEOUT"
            break
        batch = ms.models(nproc)
        if not batch:
            verdict = "UNSAT"
            break
        for a, r in pool.map(evaluate, batch):
            leaves += 1
            if r is None:
                verdict = "SAT"
                print("%s SAT fill %s" % (label, sorted(a.items())), flush=True)
                print("%s orbit consults of free rules: %d (must be 0)" % (label, orbit_consults_free(make(a))), flush=True)
                break
            name, nf, kept = r
            for ng in kept:
                sizes[len(ng)] += 1
                clauses.append(ng)
                ms.add(ng)
            if frozenset() in kept:
                verdict = "UNSAT"
                print("%s empty nogood from check %s" % (label, name), flush=True)
                break
        if not checked and len(clauses) >= 8 and label == "main":
            checked = True
            rnd = random.Random(11)
            tests = []
            for ng in clauses[-8:]:
                a = {(n, k): o for (n, k, o) in ng}
                for n in range(NL):
                    rest = [o for o in FOUT[n] if o not in {a[x] for x in a if x[0] == n}]
                    rnd.shuffle(rest)
                    for k in FREE[n]:
                        if (n, k) not in a:
                            a[(n, k)] = rest.pop()
                tests.append(a)
            res = pool.map(evaluate, tests)
            print("  soundness: %d random completions of learned nogoods, %d did NOT fail (must be 0)"
                  % (len(res), sum(1 for _, r in res if r is None)), flush=True)
        if time.time() - last > 30:
            last = time.time()
            print("  %s master=%s leaves=%d clauses=%d sizes=%s %.0fs" % (label, ms.kind, leaves, len(clauses),
                  dict(sorted(sizes.items())), time.time() - t0), flush=True)
    print("VERDICT %s %s master=%s leaves=%d clauses=%d sizes=%s %.0fs" % (verdict, label, ms.kind, leaves,
          len(clauses), dict(sorted(sizes.items())), time.time() - t0), flush=True)
    for ng in sorted(clauses, key=len)[:8]:
        print("  %s smallest nogood %d %s" % (label, len(ng), sorted(ng)), flush=True)
    return verdict


if __name__ == "__main__":
    nproc, t_pin, t_main = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    t0 = time.time()
    hctx = hierarchy_contexts(200000)
    for n in range(NL):
        FREE[n] = [k for k in DESIGN[n] if (n, k) not in hctx]
        FOUT[n] = [DESIGN[n][k] for k in FREE[n]]
        print("neighbour %d: %d hierarchy rules fixed, %d free: %s" % (n, 15 - len(FREE[n]), len(FREE[n]),
              sorted(FREE[n])), flush=True)
        print("   old free inputs inside the new free set: %s" % (OLD_FREE[n] <= set(FREE[n])), flush=True)
    print("contexts computed in %.0fs" % (time.time() - t0), flush=True)
    MODE = "planted"
    with Pool(nproc) as pool:
        solve("planted", [], nproc, 60, pool)
    MODE = "main"
    pins = [(n, k, DESIGN[n][k]) for n in range(NL) for k in FREE[n] if k not in OLD_FREE[n]]
    with Pool(nproc) as pool:
        solve("pinned", pins, nproc, t_pin, pool)
    with Pool(nproc) as pool:
        solve("main", [], nproc, t_main, pool)
