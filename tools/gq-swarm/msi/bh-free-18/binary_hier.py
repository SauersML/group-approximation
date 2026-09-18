#!/usr/bin/env python3
"""Binary move hierarchy E->ER, S->RS, R->ES (lane bh-free-18): validation, junk census, certificate.

Design: research/artifacts/gq-bh-bh-free-18-binary-hierarchy-design.md.  Letters 0, 1 (= a, E-counter),
2 (= b, S-counter).  Moving states A P X T S with a direction (> moves right, < moves left); a moving state
q becomes its reading state q' after one move.  Reading rules may look at ONE neighbour (right for the
'>' group, left for the '<' group) without changing it; for each neighbour value the reading map is a
bijection (reading states x letters) -> (moving states x letters), so F is a bijection with local inverse.
The ten unspecified reading inputs are filled by permutations pi[R] (and mirrored).

Modes:
  python3 binary_hier.py moves K        move proposition for all types, k <= K, all boundary letters
  python3 binary_hier.py junk           exhaustive entry/return census with the default fill
  python3 binary_hier.py cert FILL      full exhaustive certificate for one fill (FILL = 'default' or 15 digits)
  python3 binary_hier.py search [N]     all mirror-symmetric fills (pi[0], pi[1] = pi[2]): E/T/C/P/I filter
"""
import sys
import time
from itertools import permutations

W = 70


class Need(Exception):
    def __init__(self, k):
        self.k = k


class Fail(Exception):
    pass


DIR = {">": +1, "<": -1}
MIRROR = {">": "<", "<": ">"}

# specified reading rules for the '>' group: (state', read) -> (write, new moving state)
SPEC_R = {
    ("A>", 0): (0, "P>"), ("A>", 1): (1, "S<"), ("A>", 2): (2, "S<"),
    ("P>", 0): (0, "X<"), ("P>", 1): (1, "T<"), ("P>", 2): (2, "T<"),
    ("X<", 0): (1, "A<"),
    ("S>", 0): (2, "A>"), ("S>", 1): (0, "A>"),
}
# neighbour-conditioned specified rules: ('T<',0) if R != 0; ('S>',2) if R == 0 ; both -> (0,'S<')
FILL_IN = [("X<", 1), ("X<", 2), ("T<", 1), ("T<", 2), "U"]      # U = ('T<',0) if R==0 else ('S>',2)
FILL_OUT = [(1, "P>"), (2, "P>"), (1, "X<"), (2, "X<"), (0, "T<")]  # (write, new state)
GROUP_R = {"A>", "P>", "X<", "T<", "S>"}


def mir_state(q):
    return q[0] + MIRROR[q[1]]


def build(pi):
    """pi = {0: perm, 1: perm, 2: perm} on range(5) for the '>' group, indexed by right neighbour."""
    tab = {}
    for R in range(3):
        t = {}
        for k, v in SPEC_R.items():
            t[k] = v
        if R != 0:
            t[("T<", 0)] = (0, "S<")
        else:
            t[("S>", 2)] = (0, "S<")
        for i, inp in enumerate(FILL_IN):
            if inp == "U":
                inp = ("T<", 0) if R == 0 else ("S>", 2)
            t[inp] = FILL_OUT[pi[R][i]]
        tab[R] = t
    # check bijectivity per neighbour value (together with the mirror group, whose targets are disjoint)
    for R in range(3):
        outs = list(tab[R].values())
        if len(set(outs)) != len(outs) or len(outs) != 15:
            raise Fail("not a bijection at R=%d" % R)
    return tab


def matching(tab, q, cfg, asg):
    """q is a reading state name like 'A>' (meaning A>'); returns (write, new moving state)."""
    c = val(cfg, cfg.h, asg)
    if q in GROUP_R:
        key = (q, c)
        if key in (("T<", 0), ("S>", 2)) or key not in SPEC_R:
            n = val(cfg, cfg.h + 1, asg)
            return tab[n][key]
        return SPEC_R[key]
    # mirror group: translate to the '>' group
    mq = mir_state(q)
    key = (mq, c)
    if key in (("T<", 0), ("S>", 2)) or key not in SPEC_R:
        n = val(cfg, cfg.h - 1, asg)
        w, s = tab[n][key]
    else:
        w, s = SPEC_R[key]
    return w, mir_state(s)


class Cfg:
    __slots__ = ("t", "h", "s", "ph")

    def __init__(self, t, h, s, ph):
        self.t, self.h, self.s, self.ph = t, h, s, ph

    def copy(self):
        return Cfg(list(self.t), self.h, self.s, self.ph)


def val(cfg, i, asg):
    if i < 2 or i > len(cfg.t) - 3:
        raise Fail("window")
    c = cfg.t[i]
    if isinstance(c, tuple):
        if c[0] == "pad":
            raise Fail("pad read")
        if c[1] in asg:
            return asg[c[1]]
        raise Need(c[1])
    return c


def fresh(s, ph):
    return Cfg([("v", i - W) for i in range(2 * W + 1)], W, s, ph)


def F(tab, cfg, asg):
    if cfg.ph == 2:
        cfg.h += DIR[cfg.s[1]]
        cfg.ph = 1
    else:
        w, s = matching(tab, cfg.s, cfg, asg)
        cfg.t[cfg.h] = w
        cfg.s, cfg.ph = s, 2


def build_inverse(tab):
    outR = set(tab[0].values())
    inv = {R: {v: k for k, v in tab[R].items()} for R in range(3)}
    return outR, inv


def Finv(tab, invd, cfg, asg):
    outR, inv = invd
    if cfg.ph == 1:
        cfg.h -= DIR[cfg.s[1]]
        cfg.ph = 2
        return
    s, c = cfg.s, val(cfg, cfg.h, asg)
    if (c, s) in outR:
        n = val(cfg, cfg.h + 1, asg)
        q, a = inv[n][(c, s)]
    else:
        n = val(cfg, cfg.h - 1, asg)
        mq, a = inv[n][(c, mir_state(s))]
        q = mir_state(mq)
    cfg.t[cfg.h] = a
    cfg.s, cfg.ph = q, 1


def inY(cfg, asg):
    if cfg.ph != 2:
        return False
    s, h = cfg.s, cfg.h
    if s[0] == "A":
        return val(cfg, h, asg) != 0
    if s == "S>":
        return val(cfg, h, asg) == 0 and val(cfg, h + 1, asg) != 0
    if s == "S<":
        return val(cfg, h, asg) == 0 and val(cfg, h - 1, asg) != 0
    return False


def inA(cfg, asg):
    if cfg.ph != 2:
        return False
    s, h = cfg.s, cfg.h
    if s == "A>":
        c, n = val(cfg, h, asg), val(cfg, h + 1, asg)
        return c != 0 and (n == 0 or (c == 2 and val(cfg, h - 1, asg) == 0))
    if s == "A<":
        c, n = val(cfg, h, asg), val(cfg, h - 1, asg)
        return c != 0 and (n == 0 or (c == 2 and val(cfg, h + 1, asg) == 0))
    return False


def phi(cfg, asg):
    s, h = cfg.s, cfg.h
    if cfg.ph != 2:
        raise Fail("phi outside A")
    if s == "A>":
        if val(cfg, h + 1, asg) == 0:
            del cfg.t[h + 1]
        else:
            if val(cfg, h, asg) != 2:
                raise Fail("phi outside A")
            del cfg.t[h]
            cfg.h, cfg.s = h - 1, "S>"
    elif s == "A<":
        if val(cfg, h - 1, asg) == 0:
            del cfg.t[h - 1]
            cfg.h = h - 1
        else:
            if val(cfg, h, asg) != 2:
                raise Fail("phi outside A")
            del cfg.t[h]
            cfg.s = "S<"
    else:
        raise Fail("phi outside A")


def phi_inv(cfg, asg):
    s, h = cfg.s, cfg.h
    if s == "A>":
        cfg.t.insert(h + 1, 0)
    elif s == "A<":
        cfg.t.insert(h, 0)
        cfg.h = h + 1
    elif s == "S>":
        cfg.t.insert(h + 1, 2)
        cfg.h, cfg.s = h + 1, "A>"
    elif s == "S<":
        cfg.t.insert(h, 2)
        cfg.s = "A<"
    else:
        raise Fail("phi_inv outside Y")


def same(a, b, asg):
    if (a.s, a.ph, a.h, len(a.t)) != (b.s, b.ph, b.h, len(b.t)):
        return False
    for u, v in zip(a.t, b.t):
        if isinstance(u, tuple) and u[1] in asg:
            u = asg[u[1]]
        if isinstance(v, tuple) and v[1] in asg:
            v = asg[v[1]]
        if u != v:
            return False
    return True


CAP = {"entry": 40, "ret": 40}
STATS = {"entry": 0, "ret": 0}


def U(M, cfg, asg, inverse=False):
    for n in range(1, CAP["ret"] + 1):
        if inverse:
            Finv(M["tab"], M["inv"], cfg, asg)
        else:
            F(M["tab"], cfg, asg)
        if inY(cfg, asg):
            STATS["ret"] = max(STATS["ret"], n)
            return
    raise Fail("return > %d" % CAP["ret"])


def exhaust(states, body, stop=False, maxfail=3):
    leaves = fails = 0
    firsts = []
    for (s, ph) in states:
        stack = [{}]
        while stack:
            asg = stack.pop()
            try:
                ok = body(s, ph, asg)
            except Need as e:
                for c in range(3):
                    a2 = dict(asg)
                    a2[e.k] = c
                    stack.append(a2)
                continue
            except Fail as e:
                ok = str(e)
            leaves += 1
            if ok is not True and ok is not None:
                fails += 1
                if len(firsts) < maxfail:
                    firsts.append((s, ph, sorted(asg.items()), ok))
                if stop:
                    return leaves, fails, firsts
    return leaves, fails, firsts


NAMES = ["A>", "P>", "X>", "T>", "S>", "A<", "P<", "X<", "T<", "S<"]
ALL = [(q, ph) for q in NAMES for ph in (1, 2)]
PH2 = [(q, 2) for q in NAMES]


def body_entry(M):
    def body(s, ph, asg):
        c = fresh(s, ph)
        for n in range(CAP["entry"] + 1):
            if inY(c, asg):
                STATS["entry"] = max(STATS["entry"], n)
                U(M, c, asg)
                return True
            F(M["tab"], c, asg)
        raise Fail("entry > %d" % CAP["entry"])
    return body


def body_tower(M):
    def body(s, ph, asg):
        c = fresh(s, ph)
        if not inY(c, asg) or not inA(c, asg):
            return None
        U(M, c, asg)
        if inA(c, asg):
            raise Fail("U y in A")
        U(M, c, asg)
        if not inA(c, asg):
            raise Fail("U^2 y not in A")
        return True
    return body


def body_cover(M):
    def body(s, ph, asg):
        c = fresh(s, ph)
        if not inY(c, asg):
            return None
        if inA(c, asg):
            return True
        U(M, c, asg, inverse=True)
        if inA(c, asg):
            return True
        raise Fail("z, U^-1 z not in A")
    return body


def body_phi(M):
    def body(s, ph, asg):
        c = fresh(s, ph)
        if not inY(c, asg) or not inA(c, asg):
            return None
        y0 = c.copy()
        phi(c, asg)
        if not inY(c, asg):
            raise Fail("phi(y) not in Y")
        phi_inv(c, asg)
        return same(c, y0, asg) or "phi^-1 phi != id"
    return body


def body_phiinv(M):
    def body(s, ph, asg):
        c = fresh(s, ph)
        if not inY(c, asg):
            return None
        z0 = c.copy()
        phi_inv(c, asg)
        if not inY(c, asg) or not inA(c, asg):
            raise Fail("phi^-1 z not in A")
        phi(c, asg)
        return same(c, z0, asg) or "phi phi^-1 != id"
    return body


def body_identity(M):
    def body(s, ph, asg):
        c = fresh(s, ph)
        if not inY(c, asg) or not inA(c, asg):
            return None
        lhs = c.copy()
        U(M, lhs, asg)
        U(M, lhs, asg)
        phi(lhs, asg)
        rhs = c.copy()
        phi(rhs, asg)
        U(M, rhs, asg)
        return same(lhs, rhs, asg) or "phi U^2 != U phi"
    return body


def machine(pi):
    tab = build(pi)
    return {"tab": tab, "inv": build_inverse(tab)}


DEFAULT = {0: (0, 1, 2, 3, 4), 1: (0, 1, 2, 3, 4), 2: (0, 1, 2, 3, 4)}
