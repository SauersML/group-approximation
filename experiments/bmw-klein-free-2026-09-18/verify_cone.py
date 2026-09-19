# Independent checker for cone-propagation tree certificates (tree_<pattern>_<class>.json from dtree.py).
# Uses only the census squares and its own rewriting normal form (no lo_census code).
# A certificate is a binary tree.  ["split", g, T1, T2]: T1 assumes g in P, T2 assumes g^{-1} in P.
# ["leaf", [x, y], steps]: every step [z, u, w] asserts z = u w with u, w already in P (assumed on the
# path or derived by an earlier step), so z in P; finally x, y in P and x y = 1, a contradiction.
# Sound for a positive cone P of a left order on Gamma^+ (P P in P, P disjoint from P^{-1}, 1 not in P).
# usage: verify_cone.py census.json class tree.json
import sys, json, re
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
f, ci, tf = sys.argv[1], int(sys.argv[2]), sys.argv[3]
D = json.load(open(C + f)); iA, iB = D['iA'], D['iB']
SQ = {tuple(x): tuple(y) for x, y in D['reps'][ci]}
assert len(SQ) == len(iA) * len(iB)
def parse(s):
    w = [(c, int(x)) for c, x in re.findall(r'([hv])(\d)', s)]
    assert ''.join('%s%d' % p for p in w) == s, s
    return w
def nf(w):
    """normal form: reduced v-word followed by reduced h-word (h v -> v' h', x x^{-1} -> 1)."""
    w = list(w); i = 0
    while i < len(w) - 1:
        p, q = w[i], w[i + 1]
        if p[0] == q[0] and (iA if p[0] == 'h' else iB)[p[1]] == q[1]:
            del w[i:i + 2]; i = max(i - 1, 0); continue
        if p[0] == 'h' and q[0] == 'v':
            v2, h2 = SQ[(p[1], q[1])]; w[i], w[i + 1] = ('v', v2), ('h', h2); i = max(i - 1, 0); continue
        i += 1
    k = sum(1 for c in w if c[0] == 'v')
    assert all(c[0] == 'v' for c in w[:k]) and all(c[0] == 'h' for c in w[k:])
    return tuple(w)
# Newman: the system terminates (length or the number of h-before-v pairs drops); check the critical pairs
for h in range(len(iA)):
    for v in range(len(iB)):
        assert nf([('h', iA[h]), ('h', h), ('v', v)]) == (('v', v),)       # overlap h^-1 h | h v
        assert nf([('h', h), ('v', v), ('v', iB[v])]) == (('h', h),)       # overlap h v | v v^-1
assert all(iA[iA[x]] == x for x in range(len(iA))) and all(iB[iB[x]] == x for x in range(len(iB)))
def inv(w): return [(c, (iA if c == 'h' else iB)[x]) for c, x in reversed(w)]
def inK(w):
    n = nf(w); return sum(c == 'v' for c, _ in n) % 2 == 0 and sum(c == 'h' for c, _ in n) % 2 == 0
nsteps = nleaves = 0
def check(T, P):
    global nsteps, nleaves
    if T[0] == 'split':
        g = parse(T[1]); assert inK(g) and nf(g) != ()
        check(T[2], P | {nf(g)}); check(T[3], P | {nf(inv(g))}); return
    assert T[0] == 'leaf'
    Q = set(P)
    for z, u, w in T[2]:
        z, u, w = parse(z), parse(u), parse(w)
        assert nf(u) in Q and nf(w) in Q, 'factor not yet in P'
        assert nf(z) == nf(u + w) and inK(z) and nf(z) != (), 'bad product'
        Q.add(nf(z)); nsteps += 1
    x, y = parse(T[1][0]), parse(T[1][1])
    assert nf(x) in Q and nf(y) in Q and nf(x + y) == (), 'no contradiction'
    nleaves += 1
tree = None
for line in open(tf):
    if line.startswith('{'): tree = json.loads(line)
assert tree and tree['cls'] == ci
check(tree['tree'], frozenset())
print(f, ci, 'certificate OK:', nleaves, 'leaves,', nsteps, 'product steps; Gamma^+ is not left-orderable')
