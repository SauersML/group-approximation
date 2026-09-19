#!/usr/bin/env python3
# bh-kourovka-2146: 2-ball density certificate for one twisted Davis amalgam (Kourovka 21.46 route).
# step1: validate Radu's Gamma_{6,6,1} datum (arXiv:1712.01091, Table simple1) + permutation-routine tests.
# step2: negative control (untwisted split amalgam): local actions must stay in Sym(D^c), never dense.
# step3: twisted certificate at one vertex of each of the 128 W_1-orbit classes.
import sys, random, time
random.seed(20260918)
T0 = time.time()
def log(*a):
    print("[%7.1fs]" % (time.time() - T0), *a, flush=True)
def fail(msg):
    log("FAIL:", msg)
    sys.exit(1)

# ---------------- permutations ----------------
def compose(p, q):  # p after q
    return tuple(p[i] for i in q)
def inverse(p):
    r = [0] * len(p)
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)
def cycle_lengths(p):
    n = len(p); seen = [False] * n; out = []
    for i in range(n):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]:
                seen[j] = True; j = p[j]; l += 1
            out.append(l)
    return out
def is_even(p):
    return (len(p) - len(cycle_lengths(p))) % 2 == 0
def transitive(gens, n):
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for g in gens:
            y = g[x]
            if y not in seen:
                seen.add(y); st.append(y)
    return len(seen) == n
def primitive(gens, n):
    for j in range(1, n):
        par = list(range(n))
        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]; x = par[x]
            return x
        par[find(j)] = find(0); queue = [(0, j)]
        while queue:
            x, y = queue.pop()
            for g in gens:
                a, b = find(g[x]), find(g[y])
                if a != b:
                    par[b] = a; queue.append((g[x], g[y]))
        r0 = find(0)
        if sum(1 for i in range(n) if find(i) == r0) < n:
            return False
    return True
PRIMES = [2, 3, 5, 7, 11, 13]
def jordan_prime(p, n):
    cl = cycle_lengths(p)
    for q in PRIMES:
        if not (q <= n - 3 or (n == 5 and q == 3)):
            continue
        if cl.count(q) == 1 and all(c % q != 0 for c in cl if c != q):
            return q
    return None
def contains_alt(gens, n, tries=4000):
    """True iff certified that <gens> contains Alt(n): transitive + primitive + an element with a
    single prime cycle (Jordan, p <= n-3; for n = 5, a 3-cycle: only A5, S5 are transitive with one)."""
    gens = [g for g in gens if g != tuple(range(n))]
    if not gens or not transitive(gens, n) or not primitive(gens, n):
        return False
    for g in gens:
        if jordan_prime(g, n):
            return True
    for _ in range(tries):
        x = tuple(range(n))
        for _ in range(random.randint(1, 20)):
            x = compose(random.choice(gens), x)
        if jordan_prime(x, n):
            return True
    return False
def cyc(n, *cycles):
    p = list(range(n))
    for c in cycles:
        for i in range(len(c)):
            p[c[i]] = c[(i + 1) % len(c)]
    return tuple(p)
def perm_selftest():
    c11 = cyc(11, tuple(range(11)))
    ok = [contains_alt([cyc(11, (0, 1, 2)), c11], 11) is True,
          contains_alt([c11], 11) is False,
          contains_alt([cyc(11, (0, 1, 2)), cyc(11, (3, 4, 5))], 11) is False,
          contains_alt([cyc(6, (0, 1)), cyc(6, (0, 1, 2, 3, 4, 5))], 6) is True,
          contains_alt([cyc(6, (0, 2, 4), (1, 3, 5)), cyc(6, (0, 1), (2, 3), (4, 5))], 6) is False,
          contains_alt([cyc(5, (0, 1, 2)), cyc(5, (0, 1, 2, 3, 4))], 5) is True,
          contains_alt([cyc(5, (0, 1, 2, 3, 4)), cyc(5, (1, 4), (2, 3))], 5) is False]
    if not all(ok):
        fail("permutation self-test %s" % ok)
    log("perm self-test PASS (7 cases)")

# ---------------- Radu's Gamma_{6,6,1} ----------------
BASE = "a_1 b_1 a_2^{-1} b_1, a_1 b_2 a_2 b_2^{-1}, a_1 b_2^{-1} a_2^{-1} b_1^{-1}, a_1 b_1^{-1} a_2^{-1} b_2"
ROW1 = ("$ a_1 b_3 a_1 b_3 $, $ a_1 b_3^{-1} a_1 b_3^{-1} $, $ a_2 b_3 a_2 b_3 $, $ a_2 b_3^{-1} a_3 b_3^{-1} $, "
        "$ a_3 b_1 a_3^{-1} b_1^{-1} $, $ a_3 b_2 a_3 b_3 $, $ a_3 b_2^{-1} a_3 b_2^{-1} $")
def INV(i):
    return 7 - i  # Radu: phi(x_i) = x_{7-i} when tau = 0
def parse_tok(t):
    t = t.strip(); inv = t.endswith("^{-1}")
    if inv:
        t = t[:-5]
    kind, idx = t.split("_"); i = int(idx)
    if not 1 <= i <= 3:
        fail("bad token " + t)
    return kind, (INV(i) if inv else i)
def parse_squares(s):
    out = []
    for part in s.replace("$", "").split(","):
        toks = part.split()
        if not toks:
            continue
        if len(toks) != 4:
            fail("bad square " + part)
        k = [parse_tok(x) for x in toks]
        if [x[0] for x in k] != ["a", "b", "a", "b"]:
            fail("bad square pattern " + part)
        out.append(tuple(x[1] for x in k))
    return out
def orbit(q):
    a, b, a2, b2 = q
    return {(a, b, a2, b2), (a2, b2, a, b), (INV(a2), INV(b), INV(a), INV(b2)), (INV(a), INV(b2), INV(a2), INV(b))}
def build_datum():
    sq = parse_squares(BASE) + parse_squares(ROW1)
    if len(sq) != 11:
        fail("expected 11 squares, got %d" % len(sq))
    R = set()
    for q in sq:
        R |= orbit(q)
    return sq, R
def validate(sq, R):
    if len(R) != 36:
        fail("|R| = %d, expected 36" % len(R))
    for (i, j) in [(0, 1), (1, 2), (2, 3), (3, 0)]:
        if len({(q[i], q[j]) for q in R}) != 36:
            fail("projection (%d,%d) not bijective" % (i, j))
    for q in R:
        if not orbit(q) <= R:
            fail("R not <sigma,rho>-invariant")
    sizes = sorted(len(orbit(q)) for q in sq)
    if min(sizes) == 4:
        fail("C2xC2 acts freely: datum would be torsion-free, contradicting Radu (no torsion-free (6,6) with (*))")
    base = set()
    for q in parse_squares(BASE):
        base |= orbit(q)
    L4 = {1, 2, 5, 6}
    if len(base) != 16 or {(q[0], q[1]) for q in base} != {(x, y) for x in L4 for y in L4}:
        fail("Gamma_{4,4} sub-datum not a (4,4)-datum")
    OUT = {s: {} for s in range(1, 7)}; NXT = {s: {} for s in range(1, 7)}; ALPHA = {b: {} for b in range(1, 7)}
    for (a, b, a2, b2) in R:
        OUT[a][b] = INV(b2); NXT[a][b] = INV(a2); ALPHA[b][a2] = INV(a)
    for s in range(1, 7):
        for b in range(1, 7):
            if NXT[NXT[s][b]][INV(b)] != s or OUT[NXT[s][b]][INV(b)] != INV(OUT[s][b]):
                fail("transducer not invertible at (%d,%d)" % (s, b))
    xi = [tuple(OUT[a][b + 1] - 1 for b in range(6)) for a in range(1, 7)]
    al = [tuple(ALPHA[b][a + 1] - 1 for a in range(6)) for b in range(1, 7)]
    if not contains_alt(xi, 6):
        fail("local action on T_2 does not contain Alt(6) (Radu's (*))")
    if not contains_alt(al, 6):
        fail("local action on T_1 does not contain Alt(6) (Radu's (*))")
    log("datum PASS: 11 geometric squares (orbit sizes %s), |R|=36, 4 projections bijective, Gamma_{4,4} inside,"
        " local actions on T_1 and T_2 contain Alt(6); T_2 local action all even: %s"
          % (sizes, all(is_even(x) for x in xi)))
    return OUT, NXT
