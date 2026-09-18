# Exhaustive local certificate for the height-m renormalization of SMART_m (lane bh-free-18, 2026-09-18)

**Verdict: PASS for m = 3, 5, 7, 9, 11**, with every planted negative failing as it should.

- Run on MSI acn112, single core, under `nice` and `timeout`, with `/usr/bin/python3.11`. Each m took at most 3.1 s.
- Output is on `/projects/standard/hsiehph/sauer354/bh-free-18/`. No job was left running.
- The run was approved by the coordinator (09-18).
- Script md5: `9cbd32b03a1accd058489a7825c47a5f` (the verbatim copy is below).

## What is certified

The script covers the nodes `odd-smart-machines-have-exact-m-fold-moves` and
`odd-smart-induced-map-has-height-m-renormalization`. Notation is as in those nodes:
- `F` is the moving-head map of SMART_m;
- `Y` is the set of starts of genuine level-0 moves, and `U = F_Y`;
- `A` is the four-row local rule;
- `φ` and `φ^-1` are the four-row edit and its inverse.

**The search is exhaustive.** Each map reads only finitely many cells near the head:
- `F` reads the head cell;
- `Y` and `A` read the head cell and one neighbour;
- `U` is at most 6 steps of `F` (checked);
- `φ` and `φ^-1` touch the head cell and one neighbour.

So every identity below is decided by a bounded window. The script starts from a fully symbolic tape,
where every cell is a variable. It runs both sides of the identity, and it branches over all m letters
of a cell only when some computation actually reads that cell. At every leaf the two resulting
configurations must agree:
- the state and the head index must be equal;
- every cell must be equal, where unread cells are compared as variables, so a shift of the untouched
  tape would be caught.

This decides each identity on **all** of `Γ^Z × Q`, not on a sample. The window (radius 60) is
checked never to be reached.

| check | statement | status (m = 3, 5, 7, 9, 11) |
|---|---|---|
| R | the table is complete and reversible (the matchings are a bijection phase-1 × Γ → phase-2 × Γ) | PASS |
| M | move proposition for k ≤ 6, 5, 4, 4, 3 (m = 3, 5, 7, 9, 11), all four types and all boundary pairs: exactly f_m(k) steps, the head stays in the domain, s_+ is never written, s_* is visited only at the last step (b, d) or the first step (p, q), the tape is restored, and exactly m^k step-starts lie in Y | PASS |
| E | every configuration enters Y within 5 steps; the first return to Y takes at most 6 steps, forward and backward | PASS (max entry 5, max return 6) |
| T | for y ∈ A: U^j y ∉ A for 0 < j < m, and U^m y ∈ A | PASS |
| C | for z ∈ Y: some 0 ≤ j < m has U^-j z ∈ A | PASS |
| P | φ(A) ⊆ Y and φ^-1 φ = id on A | PASS |
| P-1 | φ^-1(Y) ⊆ A and φ φ^-1 = id on Y | PASS |
| I | φ(U^m y) = U(φ(y)) for every y ∈ A | PASS |

- T and C together give `Y = A ⊔ UA ⊔ … ⊔ U^{m-1}A` and `U^m A = A`.
- P and P-1 make `φ : A → Y` a bijection.
- I is the renormalization identity.

These are exactly the hypotheses (items 1–3) of `renormalizable-thompson-elements-give-baumslag-solitar`.
Brick-locality of `φ` and the conjugacy of `U` into `2V` are not numerical claims:
- brick-locality holds because each edit deletes a cell next to the head, or the head cell;
- the conjugacy is `brin-thompson-first-return-maps-lie-in-kv`, which needs the return bound E.

So **for each m ∈ {3, 5, 7, 9, 11}, BS(1,m) ≤ 3V is certified independently of the hand induction**, the
"one level less, one cell less" lemma with its density argument. That lemma is still what gives every
odd m. The identity I turns out to be *local*: it reads only 3 or 4 cells beyond the head. So the
certificate is a complete machine check, not only evidence.

## Calibration and blindness pre-check

- **Planted positive.** m = 3 is SMART itself, where the renormalization was refereed PASS three times
  (`smart-induced-map-has-brick-local-height-3-renormalization`). It passes.
- **Planted negatives.** Each must produce failures, and each does, for every m:
  - **neg-I and neg-P.** Row p of φ uses the wrong image state (`b_2` instead of `p_2`). For m = 5 this gives
    60 of 128 identity leaves and 20 of 68 bijection leaves failing.
  - **neg-T.** A is enlarged by "`b_2` on `x_1` with nonzero right neighbour", which starts a non-first
    sub-move of a d parent. For m = 5, 48 of 100 tower leaves fail.
  - **neg-M.** The machine has `p_1`'s two reset targets swapped. The move proposition fails at
    `b`, k = 1.

## Output (verbatim, m = 3 and m = 5; m = 7, 9, 11 have the same shape and all PASS)

```
m = 3  (0.1s)
  R                                                            PASS
  M(k<=6, longest 2185 steps)                                  PASS
  E leaves=44                                                  PASS
  T leaves=36                                                  PASS
  C leaves=28                                                  PASS
  P leaves=20                                                  PASS
  P-1 leaves=12                                                PASS
  I leaves=36                                                  PASS
  max entry 5, max return 6                                    PASS
  neg-I(row p image b2) leaves=42 fails=18                     PASS
  neg-P(row p image b2) leaves=24 fails=6                      PASS
  neg-T(A + b2 on x1) leaves=36 fails=16                       PASS
  neg-M(swapped resets): wrong end: b k=1 sp=1 ss=0 (h=5 s=q1) PASS
  ALL PASS
m = 5  (0.5s)
  R                                                            PASS
  M(k<=5, longest 7811 steps)                                  PASS
  E leaves=96                                                  PASS
  T leaves=100                                                 PASS
  C leaves=84                                                  PASS
  P leaves=52                                                  PASS
  P-1 leaves=20                                                PASS
  I leaves=100                                                 PASS
  max entry 5, max return 6                                    PASS
  neg-I(row p image b2) leaves=128 fails=60                    PASS
  neg-P(row p image b2) leaves=68 fails=20                     PASS
  neg-T(A + b2 on x1) leaves=100 fails=48                      PASS
  neg-M(swapped resets): wrong end: b k=1 sp=1 ss=0 (h=5 s=q1) PASS
  ALL PASS

m = 7, 9, 11 ALL lines:
  ALL PASS
  ALL PASS
  ALL PASS
```

## Script (verbatim)

```python
#!/usr/bin/env python3
"""Exhaustive local certificate for the height-m renormalization of SMART_m (m odd).

Nodes: research/odd-smart-machines-have-exact-m-fold-moves.md and
research/odd-smart-induced-map-has-height-m-renormalization.md (lane bh-free-18).

Every map below (F, the first return U to Y, the local rule for A, phi and phi^-1) reads only
finitely many cells near the head. So each identity is decided by a bounded window, and a lazy
depth-first search that branches over the m letters of every cell the computation actually reads
checks it on ALL configurations: unread cells stay symbolic and must match symbolically.

Checks, for each m given on the command line:
  R  the table is complete and reversible;
  M  the move proposition for k <= KMAX, every type and every boundary pair, with f_m(k) steps,
     domain confinement, s_+ never written, s_* visited only at the last (b, d) or first (p, q)
     step, and exactly m^k step-starts in Y;
  E  every configuration enters Y within 5 steps; the first return to Y takes at most 6 steps;
  T  for y in A: U^j y not in A for 0 < j < m, and U^m y in A;
  C  for z in Y: some 0 <= j < m has U^-j z in A;
  P  phi(A) is in Y with phi^-1 phi = id on A, and phi^-1(Y) is in A with phi phi^-1 = id on Y;
  I  phi(U^m y) = U(phi(y)) for every y in A.
Planted negatives (must FAIL): a wrong image state in row p of phi (I, P), an A enlarged by
b_2 on x_1 (T), and a machine with p_1's two resets swapped (M).

Usage: python3 odd_smart_certificate.py m [m ...]     (m odd >= 3; add 'neg' for negatives)
"""
import sys
import time

W = 60  # half-width of the symbolic window around the initial head


class Need(Exception):
    def __init__(self, k):
        self.k = k


class Fail(Exception):
    pass


def build(m, swap_resets=False):
    r = (m - 1) // 2
    x = lambda j: j
    y = lambda j: r + j
    move = {"b2": (+1, "b1"), "d2": (-1, "d1"), "p2": (+1, "p1"), "q2": (-1, "q1")}
    match = {}
    for c in range(m):
        match[("b1", c)] = (x(1), "d2") if c == 0 else (c, "q2")
        match[("d1", c)] = (x(1), "b2") if c == 0 else (c, "p2")
    match[("p1", 0)] = (y(1), "b2")
    match[("q1", 0)] = (y(1), "d2")
    for j in range(1, r + 1):
        if j < r:
            match[("p1", x(j))] = (x(j + 1), "d2")
            match[("p1", y(j))] = (y(j + 1), "d2")
            match[("q1", x(j))] = (x(j + 1), "b2")
            match[("q1", y(j))] = (y(j + 1), "b2")
        else:
            match[("p1", x(r))] = (0, "q2" if swap_resets else "b2")
            match[("p1", y(r))] = (0, "b2" if swap_resets else "q2")
            match[("q1", x(r))] = (0, "d2")
            match[("q1", y(r))] = (0, "p2")
    inv = {v: k for k, v in match.items()}
    unmove = {v[1]: (k, v[0]) for k, v in move.items()}
    return {"m": m, "r": r, "y1": y(1), "x1": x(1), "move": move, "match": match,
            "inv": inv, "unmove": unmove}


def check_reversible(M):
    m = M["m"]
    for q in ("b1", "d1", "p1", "q1"):
        for c in range(m):
            if (q, c) not in M["match"]:
                raise Fail("incomplete at %s,%d" % (q, c))
    if len(set(M["match"].values())) != 4 * m:
        raise Fail("matching not injective")
    if set(M["match"].values()) != {(c, q) for q in ("b2", "d2", "p2", "q2") for c in range(m)}:
        raise Fail("matching not onto phase-2 x Gamma")
    return True


# ---------------------------------------------------------------- symbolic configurations
class Cfg:
    __slots__ = ("t", "h", "s")

    def __init__(self, t, h, s):
        self.t, self.h, self.s = t, h, s

    def copy(self):
        return Cfg(list(self.t), self.h, self.s)


def val(cfg, i, asg):
    if i < 2 or i > len(cfg.t) - 3:
        raise Fail("window too small")
    c = cfg.t[i]
    if isinstance(c, tuple):
        if c[1] in asg:
            return asg[c[1]]
        raise Need(c[1])
    return c


def fresh():
    return Cfg([("v", i - W) for i in range(2 * W + 1)], W, None)


def F(M, cfg, asg):
    s = cfg.s
    if s[1] == "2":
        d, s1 = M["move"][s]
        cfg.h += d
        cfg.s = s1
    else:
        b, s2 = M["match"][(s, val(cfg, cfg.h, asg))]
        cfg.t[cfg.h] = b
        cfg.s = s2


def Finv(M, cfg, asg):
    s = cfg.s
    if s[1] == "1":
        s2, d = M["unmove"][s]
        cfg.h -= d
        cfg.s = s2
    else:
        s1, a = M["inv"][(val(cfg, cfg.h, asg), s)]
        cfg.t[cfg.h] = a
        cfg.s = s1


def inY(M, cfg, asg):
    s, h = cfg.s, cfg.h
    if s in ("b2", "d2"):
        return val(cfg, h, asg) != 0
    if s == "p2":
        return val(cfg, h + 1, asg) != 0
    if s == "q2":
        return val(cfg, h - 1, asg) != 0
    return False


def inA(M, cfg, asg, planted=False):
    s, h = cfg.s, cfg.h
    y1 = M["y1"]
    if s == "b2":
        c, rt = val(cfg, h, asg), val(cfg, h + 1, asg)
        if c == 0:
            return False
        if planted and c == M["x1"] and rt != 0:
            return True
        return rt == 0 or c == y1
    if s == "d2":
        c, lt = val(cfg, h, asg), val(cfg, h - 1, asg)
        if c == 0:
            return False
        if planted and c == M["x1"] and lt != 0:
            return True
        return lt == 0 or c == y1
    return False


STATS = {"ret": 0, "entry": 0}


def U(M, cfg, asg, inverse=False):
    step = Finv if inverse else F
    for n in range(1, 7):
        step(M, cfg, asg)
        if inY(M, cfg, asg):
            STATS["ret"] = max(STATS["ret"], n)
            return
    raise Fail("return time > 6")


def phi(M, cfg, asg, planted=False):
    s, h = cfg.s, cfg.h
    y1 = M["y1"]
    if s == "b2":
        if val(cfg, h + 1, asg) == 0:
            del cfg.t[h + 1]
        else:
            if val(cfg, h, asg) != y1:
                raise Fail("phi outside A")
            del cfg.t[h]
            cfg.h = h - 1
            cfg.s = "b2" if planted else "p2"
    elif s == "d2":
        if val(cfg, h - 1, asg) == 0:
            del cfg.t[h - 1]
            cfg.h = h - 1
        else:
            if val(cfg, h, asg) != y1:
                raise Fail("phi outside A")
            del cfg.t[h]
            cfg.s = "q2"
    else:
        raise Fail("phi outside A")


def phi_inv(M, cfg, asg):
    s, h = cfg.s, cfg.h
    y1 = M["y1"]
    if s == "b2":
        cfg.t.insert(h + 1, 0)
    elif s == "d2":
        cfg.t.insert(h, 0)
        cfg.h = h + 1
    elif s == "p2":
        cfg.t.insert(h + 1, y1)
        cfg.h = h + 1
        cfg.s = "b2"
    elif s == "q2":
        cfg.t.insert(h, y1)
        cfg.s = "d2"
    else:
        raise Fail("phi_inv outside Y")


def same(a, b, asg):
    if a.s != b.s or a.h != b.h or len(a.t) != len(b.t):
        return False
    for u, v in zip(a.t, b.t):
        if isinstance(u, tuple) and u[1] in asg:
            u = asg[u[1]]
        if isinstance(v, tuple) and v[1] in asg:
            v = asg[v[1]]
        if u != v:
            return False
    return True


# ---------------------------------------------------------------- lazy exhaustive search
def exhaust(M, states, body):
    """Run body(state, asg) over all assignments of the cells it reads. Returns (leaves, fails)."""
    m = M["m"]
    leaves = fails = 0
    first = None
    for s in states:
        stack = [{}]
        while stack:
            asg = stack.pop()
            try:
                ok = body(s, asg)
            except Need as e:
                for c in range(m):
                    a2 = dict(asg)
                    a2[e.k] = c
                    stack.append(a2)
                continue
            except Fail as e:
                ok = False
                if first is None:
                    first = (s, dict(asg), str(e))
            leaves += 1
            if ok is False:
                fails += 1
                if first is None:
                    first = (s, dict(asg), "identity false")
    return leaves, fails, first


ALL = ("b1", "b2", "d1", "d2", "p1", "p2", "q1", "q2")
PH2 = ("b2", "d2", "p2", "q2")


def body_entry(M):
    def body(s, asg):
        c = fresh()
        c.s = s
        for n in range(0, 6):
            if inY(M, c, asg):
                STATS["entry"] = max(STATS["entry"], n)
                return True
            F(M, c, asg)
        raise Fail("entry > 5")
    return body


def body_tower(M, planted=False):
    m = M["m"]

    def body(s, asg):
        c = fresh()
        c.s = s
        if not inY(M, c, asg) or not inA(M, c, asg, planted):
            return None
        for j in range(1, m + 1):
            U(M, c, asg)
            a = inA(M, c, asg, planted)
            if j < m and a:
                raise Fail("U^%d y in A" % j)
            if j == m and not a:
                raise Fail("U^m y not in A")
        return True
    return body


def body_cover(M):
    m = M["m"]

    def body(s, asg):
        c = fresh()
        c.s = s
        if not inY(M, c, asg):
            return None
        for j in range(0, m):
            if j > 0:
                U(M, c, asg, inverse=True)
            if inA(M, c, asg):
                return True
        raise Fail("no U^-j z in A")
    return body


def body_phi(M, planted=False):
    def body(s, asg):
        c = fresh()
        c.s = s
        if not inY(M, c, asg) or not inA(M, c, asg):
            return None
        y0 = c.copy()
        phi(M, c, asg, planted)
        if not inY(M, c, asg):
            raise Fail("phi(y) not in Y")
        phi_inv(M, c, asg)
        return same(c, y0, asg)
    return body


def body_phiinv(M):
    def body(s, asg):
        c = fresh()
        c.s = s
        if not inY(M, c, asg):
            return None
        z0 = c.copy()
        phi_inv(M, c, asg)
        if not inY(M, c, asg) or not inA(M, c, asg):
            raise Fail("phi^-1(z) not in A")
        phi(M, c, asg)
        return same(c, z0, asg)
    return body


def body_identity(M, planted=False):
    m = M["m"]

    def body(s, asg):
        c = fresh()
        c.s = s
        if not inY(M, c, asg) or not inA(M, c, asg):
            return None
        lhs = c.copy()
        for _ in range(m):
            U(M, lhs, asg)
        phi(M, lhs, asg, planted)
        rhs = c.copy()
        phi(M, rhs, asg, planted)
        U(M, rhs, asg)
        return same(lhs, rhs, asg)
    return body


# ---------------------------------------------------------------- the move proposition
def f(m, k):
    return (2 * m ** (k + 1) - (m + 1)) // (m - 1)


def check_moves(M, kmax):
    m = M["m"]
    worst = 0
    for k in range(0, kmax + 1):
        for t in "bdpq":
            for sp in range(1, m):
                for ss in range(m):
                    # domain cells 0..k+1 at list offset P; pads are symbolic and must not be read
                    P = 5
                    if t in "bq":
                        dom = [sp] + [0] * k + [ss]
                    else:
                        dom = [ss] + [0] * k + [sp]
                    tape = [("v", i) for i in range(P)] + dom + [("v", 100 + i) for i in range(P)]
                    lo, hi = P, P + k + 1
                    ip = lo if t in "bq" else hi          # cell of s_+
                    ist = hi if t in "bq" else lo         # cell of s_*
                    start = {"b": lo, "d": hi, "p": lo, "q": hi}[t]
                    end = {"b": hi, "d": lo, "p": hi, "q": lo}[t]
                    c = Cfg(tape, start, t + "2")
                    orig = list(tape)
                    ny = 0
                    n = f(m, k)
                    for step in range(n):
                        if not (lo <= c.h <= hi):
                            raise Fail("left domain: %s k=%d" % (t, k))
                        if c.h == ist and (t in "bd" or step != 0):
                            raise Fail("s_* visited out of turn: %s k=%d step %d" % (t, k, step))
                        try:
                            if inY(M, c, {}):
                                ny += 1
                        except Need:
                            raise Fail("Y test read a pad: %s k=%d" % (t, k))
                        before = c.t[ip]
                        try:
                            F(M, c, {})
                        except Need:
                            raise Fail("pad read: %s k=%d" % (t, k))
                        if c.t[ip] != before:
                            raise Fail("s_+ written: %s k=%d" % (t, k))
                    if c.h != end or c.s != t + "1" or c.t != orig:
                        raise Fail("wrong end: %s k=%d sp=%d ss=%d (h=%d s=%s)"
                                   % (t, k, sp, ss, c.h, c.s))
                    if ny != m ** k:
                        raise Fail("count %d != m^k=%d: %s k=%d" % (ny, m ** k, t, k))
                    worst = max(worst, n)
    return worst


def run(m, neg=False, kmax=None):
    if kmax is None:
        kmax = {3: 6, 5: 5, 7: 4, 9: 4}.get(m, 3)
    M = build(m)
    STATS["ret"] = STATS["entry"] = 0
    out = []
    t0 = time.time()
    out.append(("R", check_reversible(M)))
    out.append(("M(k<=%d, longest %d steps)" % (kmax, check_moves(M, kmax)), True))
    for name, sts, bod in (("E", ALL, body_entry(M)), ("T", PH2, body_tower(M)),
                           ("C", PH2, body_cover(M)), ("P", PH2, body_phi(M)),
                           ("P-1", PH2, body_phiinv(M)), ("I", PH2, body_identity(M))):
        leaves, fails, first = exhaust(M, sts, bod)
        out.append(("%s leaves=%d" % (name, leaves), fails == 0 if fails == 0 else (fails, first)))
    out.append(("max entry %d, max return %d" % (STATS["entry"], STATS["ret"]), True))
    if neg:
        for name, sts, bod in (("neg-I(row p image b2)", PH2, body_identity(M, planted=True)),
                               ("neg-P(row p image b2)", PH2, body_phi(M, planted=True)),
                               ("neg-T(A + b2 on x1)", PH2, body_tower(M, planted=True))):
            leaves, fails, first = exhaust(M, sts, bod)
            out.append(("%s leaves=%d fails=%d" % (name, leaves, fails), fails > 0))
        try:
            check_moves(build(m, swap_resets=True), kmax)
            out.append(("neg-M(swapped resets)", False))
        except Fail as e:
            out.append(("neg-M(swapped resets): %s" % e, True))
    print("m = %d  (%.1fs)" % (m, time.time() - t0))
    ok = True
    for name, res in out:
        print("  %-60s %s" % (name, "PASS" if res is True else res))
        ok = ok and res is True
    print("  ALL", "PASS" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    args = sys.argv[1:]
    neg = "neg" in args
    ms = [int(a) for a in args if a != "neg"] or [3]
    allok = all([run(m, neg) for m in ms])
    sys.exit(0 if allok else 1)
```
