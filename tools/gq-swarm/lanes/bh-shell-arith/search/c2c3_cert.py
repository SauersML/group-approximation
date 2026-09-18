#!/usr/bin/env python3
"""Certificate search: does R = <tau, w, b> contain Rist_V([0])?  Structured expressions, then
independent pointwise re-verification of every target found.
usage: c2c3_cert.py MODE SECONDS   MODE = twist | twistinv | untwisted
"""
import sys, random, time
from rnu_tables import compose, inverse, is_identity_leaf, merge, evaluate
from c2c3_local import (m, TAU, W3, X0, X1, A, PI_00_01, PI_00_10, canon, support_cone,
                        pull_back_from0, nontriv, carry_free)
T0 = time.time()
BUDGET = float(sys.argv[2]) if len(sys.argv) > 2 else 400.0
def left(): return BUDGET - (time.time() - T0)

MODE = sys.argv[1]
if MODE == 'twist': B = m(inverse(X1), A, X1)
elif MODE == 'twistinv': B = m(X1, A, inverse(X1))
else: B = A
GEN = {'t': TAU, 'w': W3, 'W': inverse(W3), 'b': B, 'B': inverse(B)}
TARGETS = {canon(X0): 'x0', canon(X1): 'x1', canon(TAU): 'tau', canon(PI_00_01): 'pi_00_01',
           canon(PI_00_10): 'pi_00_10'}

# expressions: global word = string over GEN; local expr: ('push', w1, w2) = local of [w1,w2]
# (conjugated by tau if its support is in [1]); ('mul', e, f); ('inv', e)
def gword(wd): return m(*[GEN[c] for c in wd]) if len(wd) > 1 else GEN[wd]
def push(k):
    c = support_cone(k)
    if c is None or c[1] == 1: return None, None
    flip = (c[0] % 2 == 1)
    if flip: k = m(TAU, k, TAU)
    return pull_back_from0(k), flip
def eval_local(e):
    if e[0] == 'push':
        g1, g2 = gword(e[1]), gword(e[2])
        k = m(g1, g2, inverse(g1), inverse(g2))
        h, flip = push(k)
        assert flip == e[3]
        return h
    if e[0] == 'mul': return merge(compose(eval_local(e[1]), eval_local(e[2])), [2])
    if e[0] == 'inv': return inverse(eval_local(e[1]))

def main():
    random.seed(5)
    pool = {}   # canon -> expr
    found = {}
    tried = 0
    while left() > BUDGET * 0.55:
        w1 = ''.join(random.choice('twWbB') for _ in range(random.randint(1, 5)))
        w2 = ''.join(random.choice('twWbB') for _ in range(random.randint(1, 5)))
        g1, g2 = gword(w1), gword(w2)
        k = m(g1, g2, inverse(g1), inverse(g2))
        tried += 1
        h, flip = push(k)
        if h is None: continue
        c = canon(h)
        if len(c) == 1 and is_identity_leaf(c[0]): continue
        if len(c) <= 16 and c not in pool: pool[c] = ('push', w1, w2, flip)
    print("== %s: phase1 %d commutators, local pool %d" % (MODE, tried, len(pool)), flush=True)
    # BFS closure among small elements
    items = list(pool.items())
    for c, e in items:
        if c in TARGETS: found.setdefault(TARGETS[c], e)
    frontier = list(items)
    rounds = 0
    while left() > 25 and len(found) < len(TARGETS):
        rounds += 1
        new = []
        base = sorted(pool.items(), key=lambda kv: len(kv[0]))[:400]
        for (c1, e1) in frontier:
            for (c2, e2) in base:
                for (h, e) in ((merge(compose(list(c1), list(c2)), [2]), ('mul', e1, e2)),
                               (merge(compose(list(c1), inverse(list(c2))), [2]), ('mul', e1, inv_expr(e2)))):
                    c = canon(h)
                    if len(c) > 10 or c in pool: continue
                    if len(c) == 1 and is_identity_leaf(c[0]): continue
                    pool[c] = e; new.append((c, e))
                    if c in TARGETS and TARGETS[c] not in found:
                        found[TARGETS[c]] = e
                        print("  FOUND", TARGETS[c], "round", rounds, "t=%ds" % (time.time() - T0), flush=True)
                if left() < 25: break
            if left() < 25: break
        frontier = new[:2000]
        print("  round %d: new %d, pool %d, found %s" % (rounds, len(new), len(pool), sorted(found)), flush=True)
        if not new: break
    # independent verification of each found target
    random.seed(99)
    for name, e in sorted(found.items()):
        h = eval_local(e)
        ok_table = canon(h) == [k for k, v in TARGETS.items() if v == name][0]
        # pointwise check of the global element behind the leaves: rebuild global element by
        # pushing forward: g = psi o h o psi^-1 on [0], identity on [1]; compare against
        # evaluating the expression's global commutators point by point
        bad = 0
        for _ in range(300):
            y = random.randint(0, 10 ** 6)
            gy = global_point(e, 2 * y)
            if gy != (0, 2 * evaluate(h, 0, y)[1]): bad += 1
            yo = 2 * y + 1
            if global_point(e, yo) != (0, yo): bad += 1
        print("  VERIFY %s: table-match=%s pointwise-bad=%d expr-size=%d" % (name, ok_table, bad, size(e)), flush=True)
        print("    EXPR", name, show(e)[:2000], flush=True)

def gpoint_word(wd, y):
    pt = (0, y)
    for c in reversed(wd):
        pt = evaluate(GEN[c], *pt)
    return pt[1]
def ginv_point_word(wd, y):
    # inverse of word applied pointwise: apply inverses of letters left to right
    inv = {'t': 't', 'w': 'W', 'W': 'w', 'b': 'B', 'B': 'b'}
    return gpoint_word(''.join(inv[c] for c in reversed(wd)), y)
def global_point(e, y):
    """Evaluate the GLOBAL element represented by local expr e (conjugated back), pointwise,
    using only generator tables (no compose/merge)."""
    if e[0] == 'push':
        w1, w2 = e[1], e[2]
        # k = g1 g2 g1^-1 g2^-1 applied right to left; possibly conjugated by tau (global)
        def k(yy):
            yy = ginv_point_word(w2, yy); yy = ginv_point_word(w1, yy)
            yy = gpoint_word(w2, yy); yy = gpoint_word(w1, yy)
            return yy
        if e[3]:
            return (0, evaluate(TAU, 0, k(evaluate(TAU, 0, y)[1]))[1])
        return (0, k(y))
    if e[0] == 'mul':
        return global_point(e[1], global_point(e[2], y)[1])
def inv_expr(e):
    if e[0] == 'push': return ('push', e[2], e[1], e[3])
    if e[0] == 'mul': return ('mul', inv_expr(e[2]), inv_expr(e[1]))
def size(e):
    return 1 if e[0] == 'push' else 1 + sum(size(x) for x in e[1:] if isinstance(x, tuple))
def show(e):
    if e[0] == 'push': return '[%s,%s]' % (e[1], e[2])
    if e[0] == 'mul': return '(%s)(%s)' % (show(e[1]), show(e[2]))
    if e[0] == 'inv': return '(%s)^-1' % show(e[1])

if __name__ == '__main__':
    main()
    print("elapsed", round(time.time() - T0), "s")