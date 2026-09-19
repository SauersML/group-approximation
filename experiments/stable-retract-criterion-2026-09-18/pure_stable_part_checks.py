#!/usr/bin/env python3
"""Decidable screen of `unit-weight-self-replicating-groups-with-pure-loops-are-not-fp`.

For a self-similar group given by a letter recursion (rooted letters with trivial
sections, state letters whose letter sections that are
words), this script checks the finite conditions of Corollary C:

  (U)  unit weight: every letter section contains at most one state letter;
  (A') the root permutations of the state letters generate a proper subgroup of P;
  (B') every weight-preserving letter section on a directed cycle of the
       weight-preserving letter graph is a single state letter (undecorated);
  (C'') at each point at most one state letter has a cycle-capable section there,
       and its root permutation fixes that point;
  (D)  for every cycle-capable state letter s of finite order, every iterated
       section of s^ord(s) is pure (a word in state letters only or rooted letters only).

It decides the word problem exactly (w = 1 iff every iterated free section has
trivial root permutation; the closure is finite because sections never raise the
weight) and computes orders of state letters up to a bound.  An infinite order is
not proved here: it is imported from the graph nodes cited in the output.

Points are coded 0..10.  Right actions: (uv)|_x = u|_x v|_{x^u}.
"""
import itertools, sys

N = 11
def perm_from_cycles(cycles):
    p = list(range(N))
    for c in cycles:
        for i, x in enumerate(c):
            p[x] = c[(i + 1) % len(c)]
    return tuple(p)
ID = tuple(range(N))
def pmul(p, q):  # first p then q
    return tuple(q[p[x]] for x in range(N))
def pinv(p):
    r = [0] * N
    for x in range(N): r[p[x]] = x
    return tuple(r)

ALPHA = perm_from_cycles([list(range(11))])
BETA = perm_from_cycles([[0, 1, 2, 3, 7], [4, 9, 6, 10, 5]])

def W(s):  # word from string like "b A a" (capital = inverse)
    out = []
    for t in s.split():
        out.append((t.lower(), -1 if t[0].isupper() else 1))
    return tuple(out)

def reduce(w):
    st = []
    for l in w:
        if st and st[-1][0] == l[0] and st[-1][1] == -l[1]: st.pop()
        else: st.append(l)
    return tuple(st)

class Rec:
    def __init__(self, name, rooted, states, sperm=None):
        self.name, self.rooted, self.states = name, rooted, states
        self.sperm = sperm or {}
    def is_state(self, l): return l in self.states
    def lperm(self, l, e):
        p = self.rooted.get(l, self.sperm.get(l, ID))
        return p if e == 1 else pinv(p)
    def lsec(self, l, e, x):
        if l in self.rooted: return ()
        if e == 1: return self.states[l].get(x, ())
        return tuple((a, -b) for a, b in reversed(self.states[l].get(x, ())))
    def perm(self, w):
        p = ID
        for l, e in w: p = pmul(p, self.lperm(l, e))
        return p
    def sec(self, w, x):
        out = []
        for l, e in w:
            out.extend(self.lsec(l, e, x))
            x = self.lperm(l, e)[x]
        return reduce(out)
    def weight(self, w): return sum(1 for l, _ in w if self.is_state(l))
    def trivial(self, w):
        seen, todo = set(), [reduce(w)]
        while todo:
            u = todo.pop()
            if u in seen or not u: continue
            seen.add(u)
            if self.perm(u) != ID: return False
            if len(seen) > 200000: raise RuntimeError("closure too large")
            for x in range(N): todo.append(self.sec(u, x))
        return True
    def order(self, l, bound=300):
        for j in range(1, bound + 1):
            if self.trivial(((l, 1),) * j): return j
        return None

def closure_group(gens):
    G, todo = {ID}, [ID]
    while todo:
        p = todo.pop()
        for g in gens:
            q = pmul(p, g)
            if q not in G: G.add(q); todo.append(q)
    return G

def fmt(u): return " ".join(l if e == 1 else l.upper() for l, e in u) or "1"

def screen(R, infinite_order_source):
    print(f"=== {R.name}")
    U = all(R.weight(w) <= 1 for s in R.states.values() for w in s.values())
    print(f"(U) unit-weight letter sections: {U}")
    P = closure_group([R.lperm(l, 1) for l in list(R.rooted) + list(R.states)])
    Pst = closure_group([R.lperm(s, 1) for s in R.states])
    Ap = len(Pst) < len(P)
    print(f"(A') |P| = {len(P)}, |P_st| = {len(Pst)} (state root perms); P_st != P: {Ap}")
    edges = {}
    for s, secs in R.states.items():
        for x, w in secs.items():
            st = [l for l, _ in w if R.is_state(l)]
            if st: edges[(s, x)] = (st[0], w)
    reach = {s: set() for s in R.states}
    for (s, x), (t, _) in edges.items(): reach[s].add(t)
    for _ in range(len(R.states)):
        for s in R.states:
            for t in list(reach[s]): reach[s] |= reach[t]
    cyc = {(s, x): (t, w) for (s, x), (t, w) in edges.items() if s in reach[t]}
    print("weight-preserving edges:", {f"{s}@{x}": fmt(w) for (s, x), (_, w) in sorted(edges.items())})
    print("cycle-capable edges:", sorted(f"{s}@{x}" for s, x in cyc))
    Bp = all(len(w) == 1 for (_, w) in cyc.values())
    print(f"(B') cycle-capable sections undecorated: {Bp}")
    pts = {}
    for (s, x) in cyc: pts.setdefault(x, set()).add(s)
    Cp = all(len(v) <= 1 and all(R.lperm(s, 1)[x] == x for s in v) for x, v in pts.items())
    print(f"(C'') one cycle-capable letter per point, fixing it: {Cp}  {dict(sorted((x, sorted(v)) for x, v in pts.items()))}")
    D = True
    for s in sorted({s for s, _ in cyc}):
        o = R.order(s)
        if o is None:
            print(f"  order({s}) > 300; infinite order imported from {infinite_order_source.get(s, '??')}")
            if s not in infinite_order_source: D = False
            continue
        seen, todo = set(), [((s, 1),) * o]
        while todo:
            u = todo.pop()
            if u in seen or not u: continue
            seen.add(u)
            for x in range(N): todo.append(R.sec(u, x))
        pure = all(all(R.is_state(l) for l, _ in u) or R.weight(u) == 0 for u in seen)
        short = sorted({fmt(u) if len(u) < 12 else f"({fmt(u[:len(u)//o])})^{o}" for u in seen})
        print(f"  order({s}) = {o}; iterated sections of {s}^{o}: {short}; pure: {pure}")
        D = D and pure
    print(f"(D) iterated sections of s^ord(s) pure for finite-order cycle letters: {D}")
    verdict = U and Ap and Bp and Cp and D
    print(f"VERDICT: Corollary C {'applies: NOT finitely presented' if verdict else 'does not apply'}")
    return verdict

ROOT = {"a": ALPHA, "e": BETA}          # a = alpha, e = beta
b = {0: W("b"), 1: W("a"), 2: W("e")}
R0 = Rec("R° = <M_11, b, C>, C = (1,1,1,C,b alpha,C^-1,1,...)", ROOT,
         {"b": b, "c": {3: W("c"), 4: W("b a"), 5: W("C")}})
R1 = Rec("R' = <M_11, b, c'>, c' = (1,1,1,c',b alpha,1,...)", ROOT,
         {"b": b, "c": {3: W("c"), 4: W("b a")}})
R2 = Rec("R'' = <M_11, b, c>, c = (c, b alpha, 1,...)", ROOT,
         {"b": b, "c": {0: W("c"), 1: W("b a")}})
src = {"c": "m11-balanced-loop-host-has-finite-h1 (R°), m11-separated-loop-host-has-b1-one (R'), m11-odometer-free-host-is-not-finitely-presented (R'')"}
res = [screen(R, src) for R in (R0, R1, R2)]

# Decorated loop b = (gamma b, alpha, beta, 1, ...) with gamma rooted fixing point 0.
def find_stab_word():
    for n in range(1, 8):
        for t in itertools.product("aAeE", repeat=n):
            w = reduce(W(" ".join(t)))
            if len(w) != n: continue
            p = Rec("", ROOT, {}).perm(w)
            if p[0] == 0 and p != ID: return " ".join(t)
g = find_stab_word()
print(f"\ngamma = {g} (rooted word fixing point 0)")
R3 = Rec(f"R_gamma = <M_11, b_g, C>, b_g = (gamma b_g, alpha, beta, 1, ...)", ROOT,
         {"b": {0: W(g + " b"), 1: W("a"), 2: W("e")}, "c": {3: W("c"), 4: W("b a"), 5: W("C")}})
srcg = {"c": "the f-orbit check at the end of this script (b_g alpha has infinite order, and C^m|_4 = (b_g alpha)^m)"}
screen(R3, srcg)
# Nielsen move g = gamma b_g (root permutation gamma, fixing 0, 1, 2); then b_g = gamma^-1 g.
gi = " ".join(t.swapcase() for t in reversed(g.split()))
R4 = Rec("R_gamma in the basis {alpha, beta, g = gamma b_g, C}", ROOT,
         {"g": {0: W("g"), 1: W("a"), 2: W("e")}, "c": {3: W("c"), 4: W(gi + " g a"), 5: W("C")}},
         sperm={"g": Rec("", ROOT, {}).perm(W(g))})
print("gamma fixes", [x for x in range(N) if R4.lperm("g", 1)[x] == x])
v4 = screen(R4, srcg)
print("\nsummary:", {"R°": res[0], "R'": res[1], "R''": res[2], "R_gamma (after Nielsen move)": v4})

# Infinite order of b_g alpha in R_gamma (so C has infinite order there: C^m|_4 = (b_g alpha)^m).
# For h = b_g rho (rho in M_11 rooted), let l = length of the rho-cycle of 0.  Then h^l|_0 =
# gamma b_g tau, with tau the product of b_g|_1 = alpha, b_g|_2 = beta met along that cycle, and
# gamma^-1 (gamma b_g tau) gamma = b_g f(rho) with f(rho) = tau gamma.  All other cycles give rooted
# sections, so ord(h) >= l * ord(b_g f(rho)) when finite.  If the eventual f-cycle of rho contains
# some rho* with l(rho*) >= 2, then ord(b_g rho*) >= 2^k for every k, so b_g rho has infinite order.
def loop_orbit(rho, gam):
    SEC = {1: ALPHA, 2: BETA}
    seen, seq = {}, []
    while rho not in seen:
        seen[rho] = len(seq)
        cyc, x = [0], rho[0]
        while x != 0: cyc.append(x); x = rho[x]
        tau = ID
        for y in cyc[1:]:
            if y in SEC: tau = pmul(tau, SEC[y])
        seq.append((rho, len(cyc)))
        rho = pmul(tau, gam)
    per = seq[seen[rho]:]
    return [l for _, l in seq], [l for _, l in per]
GAM = Rec("", ROOT, {}).perm(W(g))
for name, gam, rho in (("R_gamma: b_g alpha", GAM, ALPHA), ("R°: b alpha (gamma = 1)", ID, ALPHA),
                       ("R_gamma: b_g", GAM, ID)):
    pre, per = loop_orbit(rho, gam)
    print(f"{name}: cycle lengths of 0 along f-orbit {pre}; periodic part {per}; "
          f"{'INFINITE order' if max(per) >= 2 else 'no conclusion (finite-order pattern)'}")
