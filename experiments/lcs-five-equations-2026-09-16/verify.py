#!/usr/bin/env python3
"""Exact checks for the five-equation LCS theorem (2026-09-16).

Part 1  Mermin pentagram as a K_5 incidence solution.
        Ten 3-qubit Pauli operators, one per edge of K_5, five vertex equations.
        Exact Gaussian-integer arithmetic: involutions, commutation inside every
        vertex equation, vertex products = +-I with odd total parity.  Then, for
        each of the 16 odd right-hand sides b in F_2^5, an explicit edge sign-flip
        set is produced and the whole solution is re-verified exactly.

Part 2  Commutation closure in the generic-sign incidence group H(G).
        Rule: if column y commutes with every column of row v except e, then y
        commutes with e (c_v is central).  Replays the derivations used in the
        proof for K_4 (closure complete) and K_5 minus an edge (t12,t13,t23
        central), and confirms that the rule derives nothing for K_5.

Part 3  Census over all 1024 labelled graphs on 5 vertices: which have complete
        commutation closure (informational only; the proof does not use it).
"""
import itertools, sys

# ---------------------------------------------------------------- Gaussian ints
def gmul(a, b):
    return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0])

def gadd(a, b):
    return (a[0]+b[0], a[1]+b[1])

def mmul(A, B):
    n = len(A)
    C = [[(0, 0)]*n for _ in range(n)]
    for i in range(n):
        for k in range(n):
            if A[i][k] != (0, 0):
                aik = A[i][k]
                for j in range(n):
                    if B[k][j] != (0, 0):
                        C[i][j] = gadd(C[i][j], gmul(aik, B[k][j]))
    return C

def kron(A, B):
    n, m = len(A), len(B)
    return [[gmul(A[i//m][j//m], B[i % m][j % m]) for j in range(n*m)] for i in range(n*m)]

def ident(n):
    return [[(1, 0) if i == j else (0, 0) for j in range(n)] for i in range(n)]

def scal(s, A):
    return [[gmul(s, x) for x in row] for row in A]

PI = ident(2)
PX = [[(0, 0), (1, 0)], [(1, 0), (0, 0)]]
PY = [[(0, 0), (0, -1)], [(0, 1), (0, 0)]]
PAULI = {'I': PI, 'X': PX, 'Y': PY}

def op(word):
    M = PAULI[word[0]]
    for ch in word[1:]:
        M = kron(M, PAULI[ch])
    return M

I8 = ident(8)
MINUS = (-1, 0)

# vertices 0..4 of K_5 = the five lines of the pentagram; edges = the ten points
EDGE_OP = {
    (0, 1): 'XXX', (0, 2): 'XYY', (0, 3): 'YXY', (0, 4): 'YYX',
    (1, 2): 'XII', (1, 3): 'IXI', (1, 4): 'IIX',
    (2, 3): 'IIY', (2, 4): 'IYI', (3, 4): 'YII',
}
EDGES = sorted(EDGE_OP)
assert len(EDGES) == 10 and set(EDGES) == set(itertools.combinations(range(5), 2))

def sign_of_scalar(M):
    """Return +1 / -1 if M = +-I exactly, else None."""
    if M == I8:
        return 1
    if M == scal(MINUS, I8):
        return -1
    return None

def verify_solution(ops, b):
    """ops: edge -> 8x8 matrix.  Check involution, commutation in each vertex
    equation, vertex product = (-1)^b_v I.  Returns list of failures."""
    fails = []
    for e, M in ops.items():
        if mmul(M, M) != I8:
            fails.append(('not involution', e))
    for v in range(5):
        inc = [e for e in EDGES if v in e]
        for e, f in itertools.combinations(inc, 2):
            if mmul(ops[e], ops[f]) != mmul(ops[f], ops[e]):
                fails.append(('noncommuting in equation', v, e, f))
        P = I8
        for e in inc:
            P = mmul(P, ops[e])
        s = sign_of_scalar(P)
        want = -1 if b[v] else 1
        if s != want:
            fails.append(('bad vertex product', v, s, want))
    return fails

def part1():
    ops = {e: op(w) for e, w in EDGE_OP.items()}
    b0 = []
    for v in range(5):
        P = I8
        for e in EDGES:
            if v in e:
                P = mmul(P, ops[e])
        s = sign_of_scalar(P)
        assert s is not None, 'vertex product not scalar'
        b0.append(0 if s == 1 else 1)
    print('pentagram base right-hand side b0 =', b0, ' parity', sum(b0) % 2)
    f0 = verify_solution(ops, b0)
    print('base solution failures:', f0)
    assert not f0 and sum(b0) % 2 == 1
    # spanning star at vertex 0: flipping edge (0,v) toggles b_0 and b_v
    count = 0
    for b in itertools.product((0, 1), repeat=5):
        if sum(b) % 2 != 1:
            continue
        d = [(b[v] + b0[v]) % 2 for v in range(5)]
        flips = [(0, v) for v in range(1, 5) if d[v]]
        # parity of d is even, so toggling b_0 by len(flips) matches d[0]
        assert len(flips) % 2 == d[0]
        new = {e: (scal(MINUS, M) if e in flips else M) for e, M in ops.items()}
        f = verify_solution(new, list(b))
        assert not f, (b, f)
        count += 1
    print('odd right-hand sides verified with explicit 8-dim solutions:', count)
    assert count == 16

# ---------------------------------------------------------------- closure
def closure(nverts, columns):
    """columns: list of frozensets of rows.  Returns set of commuting index pairs."""
    k = len(columns)
    comm = set()
    for i in range(k):
        for j in range(k):
            if i == j or columns[i] & columns[j]:
                comm.add((i, j))
    rows = [[i for i in range(k) if v in columns[i]] for v in range(nverts)]
    derivations = []
    changed = True
    while changed:
        changed = False
        for y in range(k):
            for v in range(nverts):
                missing = [e for e in rows[v] if (y, e) not in comm]
                if len(missing) == 1:
                    e = missing[0]
                    comm.add((y, e)); comm.add((e, y))
                    derivations.append((y, e, v))
                    changed = True
    return comm, derivations

def name(c):
    return ''.join(str(x + 1) for x in sorted(c))

def report(label, nverts, cols):
    comm, der = closure(nverts, cols)
    k = len(cols)
    central = [name(cols[i]) for i in range(k) if all((i, j) in comm for j in range(k))]
    nonc = sorted({tuple(sorted((name(cols[i]), name(cols[j])))) for i in range(k)
                   for j in range(k) if (i, j) not in comm})
    print(f'{label}: {k} columns, derived {len(der)} commutations')
    for y, e, v in der:
        print(f'   x{name(cols[y])} commutes with x{name(cols[e])}   (row {v+1})')
    print('   central columns:', central)
    print('   remaining noncommuting pairs:', nonc)
    return comm, central, nonc

def part2():
    K4 = [frozenset(p) for p in itertools.combinations(range(4), 2)]
    _, c4, n4 = report('K_4', 4, K4)
    assert not n4
    K5e = [frozenset(p) for p in itertools.combinations(range(5), 2) if p != (3, 4)]
    _, c5e, n5e = report('K_5 minus 45', 5, K5e)
    assert {'12', '13', '23'} <= set(c5e)
    K5 = [frozenset(p) for p in itertools.combinations(range(5), 2)]
    _, _, n5 = report('K_5', 5, K5)
    assert len(n5) == 15
    # weight-4 columns are central whenever |S| <= 5 (initial commutations)
    for S in (4, 5):
        cols = [frozenset(p) for r in (2, 4) for p in itertools.combinations(range(S), r)]
        comm, _ = closure(S, cols)
        for i, c in enumerate(cols):
            if len(c) == 4:
                assert all(c & d for d in cols), (S, c)
    print('weight-4 columns meet every even column when |S| <= 5: ok')

def part3():
    pairs = list(itertools.combinations(range(5), 2))
    complete = 0
    for mask in range(1 << 10):
        cols = [frozenset(pairs[i]) for i in range(10) if mask >> i & 1]
        comm, _ = closure(5, cols)
        if len(comm) == len(cols) ** 2:
            complete += 1
    print('labelled graphs on 5 vertices with complete closure:', complete, 'of 1024')

if __name__ == '__main__':
    part1()
    part2()
    part3()
    print('ALL CHECKS PASSED')
