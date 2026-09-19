"""Checks for fpbs-branching-barrier-certificates-spectral-floor.

1. Stallings folding of phi(H) = <a, b a b^-2> in F(a, b): the child cosets
   b^-1 phi(H) and a b^-2 phi(H) COINCIDE (c_3 = c_1 b in M), so the child
   graph is a DAG with merges (c_3 c_2 = c_1 c_1), not a ternary tree.  The
   floor theorem does not use tree structure.
2. The child differences c_i c_j^-1 for c_1 = b^-1 t, c_2 = b^-2 t,
   c_3 = a b^-2 t are b^{+-1}, a^{+-1}, (b a^-1)^{+-1}.
3. Constants: kappa = 4 - 2 sqrt 3 (Kesten), eta = kappa / 4, and the floor
   delta_* = positive root of eta d^2 + 4 d - eta = 0.
4. Brute-force the recurrence: smallest delta for which a sequence
   alpha_0 = 1 - delta, alpha_{j+1} in [alpha_j + eta a(1-a) - delta, alpha_j]
   can reach 0.  Matches delta_* up to grid error.
"""
from fractions import Fraction
import math

# ---------- free group words: letters 'a','A','b','B' (capital = inverse)
INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def reduce(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


def inv(w):
    return ''.join(INV[c] for c in reversed(w))


def stallings(gens):
    """Folded core graph: vertices ints, edges (u, letter, v) for positive letters."""
    edges = {}  # (u, letter) -> v, letter in a,A,b,B
    nv = [1]

    def add(u, c, v):
        edges.setdefault((u, c), set()).add(v)
        edges.setdefault((v, INV[c]), set()).add(u)

    for g in gens:
        u = 0
        for i, c in enumerate(g):
            v = 0 if i == len(g) - 1 else nv[0]
            if i != len(g) - 1:
                nv[0] += 1
            add(u, c, v)
            u = v
    # fold
    changed = True
    while changed:
        changed = False
        for key, targets in list(edges.items()):
            if len(targets) > 1:
                ts = sorted(targets)
                keep, drop = ts[0], ts[1]
                # merge drop into keep
                new = {}
                for (u, c), vs in edges.items():
                    u2 = keep if u == drop else u
                    vs2 = {keep if v == drop else v for v in vs}
                    new.setdefault((u2, c), set()).update(vs2)
                edges.clear()
                edges.update(new)
                changed = True
                break
    return edges


def member(edges, w):
    u = 0
    for c in reduce(w):
        vs = edges.get((u, c))
        if not vs:
            return False
        (u,) = tuple(vs)
    return u == 0


phiH = stallings([reduce('a'), reduce('baBB')])
verts = {u for (u, _) in phiH}
print('core graph of phi(H): vertices', sorted(verts))
for (u, c), vs in sorted(phiH.items()):
    if c in 'ab':
        print('  ', u, c, '->', sorted(vs))
assert member(phiH, 'a') and member(phiH, 'baBB')
assert not member(phiH, 'b')

h = {'c1': 'B', 'c2': 'BB', 'c3': 'aBB'}
names = list(h)
same = {}
for i in names:
    for j in names:
        if i < j:
            d = reduce(inv(h[j]) + h[i])
            same[(i, j)] = member(phiH, d)
            print('coset test', i, j, 'h_j^-1 h_i =', d, 'in phi(H):', same[(i, j)])
# Result: c1 and c3 lie in the same left phi(H)-coset (c3 = c1 b), the others
# are distinct.  So the child graph is NOT a tree: c3 c2 = c1 b c2 = c1 c1.
assert same[('c1', 'c3')] and not same[('c1', 'c2')] and not same[('c2', 'c3')]
print('c3 = c1 b, hence c3 c2 = c1 c1: the child graph is a DAG with merges')
# b^k never in phi(H) for k != 0 (b-reading leaves the base vertex)
for k in range(1, 12):
    assert not member(phiH, 'b' * k) and not member(phiH, 'B' * k)
print('b^k not in phi(H) for 1<=|k|<12')

# ---------- child differences c_i c_j^-1 = h_i t t^-1 h_j^-1 = h_i h_j^-1
for i in names:
    for j in names:
        if i != j:
            print('c_%s c_%s^-1 =' % (i[1], j[1]), reduce(h[i] + inv(h[j])))

# ---------- constants
kappa = 4 - 2 * math.sqrt(3)
eta = kappa / 4
# delta_* = positive root of eta d^2 + 4 d - eta = 0, i.e. the delta at which the
# forbidden interval (r_-, r_+) of eta r (1 - r) > delta has width exactly delta.
dstar = (math.sqrt(4 + eta * eta) - 2) / eta
width = math.sqrt(1 - 4 * dstar / eta)
assert abs(width - dstar) < 1e-12
print('kappa = %.6f  eta = %.6f  delta_* = %.6f' % (kappa, eta, dstar))


# ---------- brute force the recurrence (greedy is optimal: go down as fast as allowed)
def reaches_zero(delta, steps=10 ** 6):
    a = 1 - delta
    for _ in range(steps):
        lo = a + eta * a * (1 - a) - delta
        if lo > a:  # constraint alpha_{j+1} <= alpha_j violated: stuck forever
            return False
        a = max(lo, 0.0)
        if a <= 1e-12:
            return True
    return False


lo, hi = 0.0, 0.5
for _ in range(50):
    mid = (lo + hi) / 2
    if reaches_zero(mid, 20000):
        hi = mid
    else:
        lo = mid
print('numerical least delta reaching 0: %.6f (analytic lower bound %.6f)' % (hi, dstar))
assert hi >= dstar - 1e-6
