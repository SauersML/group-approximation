"""Phase-tube calibration for coset lifts (swarm-0917-w21-w21-gs-last1, 2026-09-20).

Symbols over an output alphabet A = {0,...,q-1}, distinguished letter a = 0:
  ('P', u, p)  phase symbol, u in A, p in {0,1}   output u
  ('B',)       break symbol                       output a
  ('S', u)     star symbol, u in A                 output f(u) = 1 + (u mod (q-1))  (onto A minus {a})
2-block rule: adjacent phase symbols must have opposite phases; two adjacent breaks are forbidden.

Checks:
  1. single-site lifts: for every left/right neighbour pair and every target letter b there is a
     centre symbol with output b compatible with both neighbours (so the 1-block code is strongly
     post-surjective with Phi = {0} and onto A^Z);
  2. the constant point ('S',0)^infinity is allowed;
  3. the fibre over a^infinity: trace of the fibre transition matrix (sigma-fixed points) is 0,
     trace of its square (period-2 points) is positive;
  4. the same on cycles Z/n: the fibre over the constant a^n is nonempty and has no rotation-fixed point.
"""
import itertools
import sys


def symbols(q):
    s = [('P', u, p) for u in range(q) for p in (0, 1)]
    s.append(('B',))
    s += [('S', u) for u in range(q)]
    return s


def out(s, q):
    if s[0] == 'P':
        return s[1]
    if s[0] == 'B':
        return 0
    return 1 + (s[1] % (q - 1))


def ok(s, t):
    if s[0] == 'P' and t[0] == 'P':
        return s[2] != t[2]
    if s[0] == 'B' and t[0] == 'B':
        return False
    return True


def check(q):
    S = symbols(q)
    # 1. single-site lifts
    for l, r in itertools.product(S, S):
        for b in range(q):
            if not any(out(c, q) == b and ok(l, c) and ok(c, r) for c in S):
                return f"lift fails q={q} l={l} r={r} b={b}"
    # 2. constant star point
    assert ok(('S', 0), ('S', 0))
    # 3. fibre transition matrix over a
    fib = [s for s in S if out(s, q) == 0]
    tr1 = sum(1 for s in fib if ok(s, s))
    tr2 = sum(1 for s in fib for t in fib if ok(s, t) and ok(t, s))
    if tr1 != 0 or tr2 == 0:
        return f"fibre traces wrong q={q}: tr1={tr1} tr2={tr2}"
    # 4. cycles
    for n in range(3, 9):
        count = 0
        fixed = 0
        for w in itertools.product(fib, repeat=n):
            if all(ok(w[i], w[(i + 1) % n]) for i in range(n)):
                count += 1
                if len(set(w)) == 1:
                    fixed += 1
        if count == 0 or fixed != 0:
            return f"cycle n={n} q={q}: fibre points={count}, rotation-fixed={fixed}"
    return f"q={q}: lifts ok; fibre tr(M)={tr1}, tr(M^2)={tr2}; cycles 3..8 nonempty, no fixed point"


if __name__ == '__main__':
    bad = False
    for q in (2, 3, 4):
        msg = check(q)
        print(msg)
        bad |= not msg.startswith(f"q={q}:")
    sys.exit(1 if bad else 0)
