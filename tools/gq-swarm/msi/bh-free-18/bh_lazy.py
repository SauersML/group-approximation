#!/usr/bin/env python3
"""Lazy backtracking search over the fill of binary_hier.py (lane bh-free-18).

A fill entry (neighbour value R, reading input) is chosen only when some configuration of the exhaustive
certificate actually uses it (forward), or when an inverse step meets an output no input yet produces.
Checks: R, T, C2, P, P-1, I of bh_run.py (the renormalization criterion; no global entry bound).
Usage: python3 bh_lazy.py [maxsol]
"""
import sys
import time
import binary_hier as B
import bh_run as H


class NeedFill(Exception):
    def __init__(self, R, key, inv):
        self.R, self.key, self.inv = R, key, inv


def resolve(inp, R):
    if inp == "U":
        return ("T<", 0) if R == 0 else ("S>", 2)
    return inp


FILL_KEYS = {R: [resolve(i, R) for i in B.FILL_IN] for R in range(3)}
OUT_R = set(B.SPEC_R.values()) | {(0, "S<")} | set(B.FILL_OUT)
assert len(OUT_R) == 15


def make(assign):
    tab = {}
    for R in range(3):
        t = dict(B.SPEC_R)
        if R != 0:
            t[("T<", 0)] = (0, "S<")
        else:
            t[("S>", 2)] = (0, "S<")
        for (RR, key), out in assign.items():
            if RR == R:
                t[key] = out
        tab[R] = t
    inv = {R: {v: k for k, v in tab[R].items()} for R in range(3)}
    return {"tab": tab, "inv": (OUT_R, inv)}


def matching(tab, q, cfg, asg):
    c = B.val(cfg, cfg.h, asg)
    grp = q in B.GROUP_R
    key = (q if grp else B.mir_state(q), c)
    if key in (("T<", 0), ("S>", 2)) or key not in B.SPEC_R:
        n = B.val(cfg, cfg.h + 1 if grp else cfg.h - 1, asg)
        if key not in tab[n]:
            raise NeedFill(n, key, False)
        w, s = tab[n][key]
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
        if (c, s) not in inv[n]:
            raise NeedFill(n, (c, s), True)
        q, a = inv[n][(c, s)]
    else:
        n = B.val(cfg, cfg.h - 1, asg)
        o = (c, B.mir_state(s))
        if o not in inv[n]:
            raise NeedFill(n, o, True)
        mq, a = inv[n][o]
        q = B.mir_state(mq)
    cfg.t[cfg.h] = a
    cfg.s, cfg.ph = q, 1


B.matching = matching
B.Finv = Finv

NODES = [0]
SOLS = []


def solve(assign, maxsol):
    NODES[0] += 1
    M = make(assign)
    for name, sts, mk in H.CHECKS2:
        try:
            leaves, fails, first = B.exhaust(sts, mk(M), stop=True)
        except NeedFill as e:
            used_out = {assign[k] for k in assign if k[0] == e.R}
            used_in = {k[1] for k in assign if k[0] == e.R}
            if not e.inv:
                for out in B.FILL_OUT:
                    if out not in used_out:
                        a2 = dict(assign)
                        a2[(e.R, e.key)] = out
                        solve(a2, maxsol)
                        if len(SOLS) >= maxsol:
                            return
            else:
                if e.key in used_out or e.key not in B.FILL_OUT:
                    return
                for key in FILL_KEYS[e.R]:
                    if key not in used_in:
                        a2 = dict(assign)
                        a2[(e.R, key)] = e.key
                        solve(a2, maxsol)
                        if len(SOLS) >= maxsol:
                            return
            return
        if fails:
            DEAD[name] = DEAD.get(name, 0) + 1
            if len(DEADEX.setdefault(name, [])) < 3:
                DEADEX[name].append((sorted(assign.items()), first[:1]))
            return
    SOLS.append(sorted(assign.items()))
    print("SOLUTION", sorted(assign.items()), flush=True)


DEAD = {}
DEADEX = {}

if __name__ == "__main__":
    maxsol = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    t0 = time.time()
    solve({}, maxsol)
    print("nodes=%d solutions=%d dead=%s %.0fs" % (NODES[0], len(SOLS), DEAD, time.time() - t0))
    for k, v in DEADEX.items():
        for x in v:
            print("DEAD", k, x)
