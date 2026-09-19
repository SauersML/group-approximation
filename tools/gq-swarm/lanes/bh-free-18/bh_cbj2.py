#!/usr/bin/env python3
"""Complete search (v2: global store of learned leaf nogoods) over the fill of binary_hier.py with conflict-directed backjumping (lane bh-free-18).

Variables: for each right-neighbour value R in {0,1,2}, a bijection from the 5 unspecified reading inputs to the 5
unused outputs. A fill entry is branched on only when some certificate computation consults it, forwards (F) or
backwards (F^-1). Every failing computation returns the exact set of fill facts (R, input, output) it consulted,
so a failure is a nogood; a subtree whose children all fail returns the union of their nogoods minus the branch
fact (plus the facts that excluded values by injectivity). Checks: R, T, C2, P, P-1, I (bh_run.CHECKS2).
Output: every solution, or the root nogood (a proof that no fill works), with the witness configurations.
Usage: python3 bh_cbj.py
"""
import sys
import time
import binary_hier as B
import bh_run as H
import bh_lazy as L

LOG = set()


class NeedFill(Exception):
    def __init__(self, R, key, inv):
        self.R, self.key, self.inv = R, key, inv


def matching(tab, q, cfg, asg):
    c = B.val(cfg, cfg.h, asg)
    grp = q in B.GROUP_R
    key = (q if grp else B.mir_state(q), c)
    if key in (("T<", 0), ("S>", 2)) or key not in B.SPEC_R:
        n = B.val(cfg, cfg.h + 1 if grp else cfg.h - 1, asg)
        if key not in tab[n]:
            raise NeedFill(n, key, False)
        w, s = tab[n][key]
        if key in L.FILL_KEYS[n]:
            LOG.add((n, key, (w, s)))
    else:
        w, s = B.SPEC_R[key]
    return (w, s) if grp else (w, B.mir_state(s))


def Finv(tab, invd, cfg, asg):
    outR, inv = invd
    if cfg.ph == 1:
        cfg.h -= B.DIR[cfg.s[1]]
        cfg.ph = 2
        return
    s, c = cfg.s, B.val(cfg, cfg.h, asg)
    if (c, s) in outR:
        n = B.val(cfg, cfg.h + 1, asg)
        o = (c, s)
        mirror = False
    else:
        n = B.val(cfg, cfg.h - 1, asg)
        o = (c, B.mir_state(s))
        mirror = True
    if o not in inv[n]:
        raise NeedFill(n, o, True)
    q, a = inv[n][o]
    if o in B.FILL_OUT:
        LOG.add((n, (q, a), o))
    if mirror:
        q = B.mir_state(q)
    cfg.t[cfg.h] = a
    cfg.s, cfg.ph = q, 1


B.matching = matching
B.Finv = Finv


def run_checks(M):
    """Return ('ok',) or ('need', NeedFill) or ('fail', name, facts, witness)."""
    for name, sts, mk in H.CHECKS2:
        body = mk(M)
        for (s, ph) in sts:
            stack = [{}]
            while stack:
                asg = stack.pop()
                LOG.clear()
                try:
                    ok = body(s, ph, asg)
                except B.Need as e:
                    for c in range(3):
                        a2 = dict(asg)
                        a2[e.k] = c
                        stack.append(a2)
                    continue
                except NeedFill as e:
                    return ("need", e)
                except B.Fail as e:
                    ok = str(e)
                if ok is not True and ok is not None:
                    return ("fail", name, frozenset(LOG), (s, ph, sorted(asg.items()), ok))
    return ("ok",)


STATS = {"nodes": 0, "jumps": 0, "hits": 0}
STORE = []
WITNESS = {}
SOLS = []


def search(assign):
    """assign: dict (R, key) -> out. Returns None if a solution was found below, else a nogood (frozenset of facts)."""
    STATS["nodes"] += 1
    if STATS["nodes"] % 500 == 0:
        print("  nodes=%d jumps=%d hits=%d store=%d depth=%d %.0fs" % (STATS["nodes"], STATS["jumps"], STATS["hits"], len(STORE), len(assign), time.time() - T0), flush=True)
    facts = {(RR, k, o) for (RR, k), o in assign.items()}
    for ng0 in STORE:
        if ng0 <= facts:
            STATS["hits"] += 1
            return ng0
    M = L.make(assign)
    r = run_checks(M)
    if r[0] == "ok":
        SOLS.append(sorted(assign.items()))
        print("SOLUTION", sorted(assign.items()), flush=True)
        return None
    if r[0] == "fail":
        _, name, facts, wit = r
        WITNESS.setdefault(facts, (name, wit))
        STORE.append(facts)
        return facts
    e = r[1]
    R = e.R
    conflict = set()
    found = False
    if not e.inv:
        taken = {o: k for (RR, k), o in assign.items() if RR == R}
        for o in B.FILL_OUT:
            if o in taken:
                conflict.add((R, taken[o], o))
                continue
            fact = (R, e.key, o)
            a2 = dict(assign)
            a2[(R, e.key)] = o
            ng = search(a2)
            if ng is None:
                found = True
                continue
            if fact not in ng:
                STATS["jumps"] += 1
                return ng
            conflict |= ng - {fact}
    else:
        o = e.key
        if o not in B.FILL_OUT:
            raise RuntimeError("inverse needs a non-fill output %r" % (o,))
        used = {k: oo for (RR, k), oo in assign.items() if RR == R}
        for key in L.FILL_KEYS[R]:
            if key in used:
                conflict.add((R, key, used[key]))
                continue
            fact = (R, key, o)
            a2 = dict(assign)
            a2[(R, key)] = o
            ng = search(a2)
            if ng is None:
                found = True
                continue
            if fact not in ng:
                STATS["jumps"] += 1
                return ng
            conflict |= ng - {fact}
    if found:
        return None
    ng = frozenset(conflict)
    STORE.append(ng)
    return ng


if __name__ == "__main__":
    T0 = time.time()
    sys.setrecursionlimit(10000)
    ng = search({})
    print("DONE nodes=%d jumps=%d solutions=%d %.0fs" % (STATS["nodes"], STATS["jumps"], len(SOLS), time.time() - T0))
    if ng is not None:
        print("ROOT NOGOOD", sorted(ng), "(empty = no fill passes the criterion)")
    # witnesses of the smallest nogoods
    for facts, (name, wit) in sorted(WITNESS.items(), key=lambda kv: len(kv[0]))[:12]:
        print("WITNESS |facts|=%d %s %s" % (len(facts), name, str(wit)[:300]), sorted(facts))
