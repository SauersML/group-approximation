#!/usr/bin/env python3
"""Section-invariant characters psi: H -> Q (psi(h) = sum_x psi(h|_x)) for test automata,
plus checks used in basilica-rn-group-is-not-a-k-graph-full-group-proof.

A. Solve the linear conditions psi(g) = sum_x psi(g|_x) on generators (with involution /
   known relators imposed), over Q.
B. For the contracting examples, decide triviality of every freely reduced word of length
   <= L exactly (coinductive section recursion) and check that trivial words have psi = 0.
C. Koszul lemma: for random commuting integer pairs (A, B=p(A)), H_0 of the Koszul complex
   of (1-A, 1-B) over Q vanishes only if all of its homology vanishes.
Run: python3 section_characters.py > results-section-characters.txt
"""
import itertools, random
from sympy import Matrix, Rational, eye, zeros

# automaton: gen -> (perm as tuple image of x, [section word for each x]); word = tuple of (gen, +-1)
A = {
 'basilica': {'a': ((1, 0), [(), (('b', 1),)]), 'b': ((0, 1), [(), (('a', 1),)])},
 'odometer': {'a': ((1, 0), [(), (('a', 1),)])},
 'lamplighter': {'a': ((1, 0), [(('a', 1),), (('b', 1),)]), 'b': ((0, 1), [(('a', 1),), (('b', 1),)])},
 'grigorchuk': {'a': ((1, 0), [(), ()]), 'b': ((0, 1), [(('a', 1),), (('c', 1),)]),
                'c': ((0, 1), [(('a', 1),), (('d', 1),)]), 'd': ((0, 1), [(), (('b', 1),)])},
 'hanoi3': {'a': ((1, 0, 2), [(), (), (('a', 1),)]), 'b': ((2, 1, 0), [(), (('b', 1),), ()]),
            'c': ((0, 2, 1), [(('c', 1),), (), ()])},
}
INVOL = {'grigorchuk': 'abcd', 'hanoi3': 'abc'}
EXTRA = {'grigorchuk': [(('b', 1), ('c', 1), ('d', 1))]}

def letter(aut, g, e):
    perm, secs = aut[g]
    d = len(perm)
    if e == 1:
        return perm, [tuple(s) for s in secs]
    inv = [0] * d
    for x in range(d):
        inv[perm[x]] = x
    return tuple(inv), [tuple((h, -f) for (h, f) in reversed(secs[inv[x]])) for x in range(d)]

def reduce(w):
    out = []
    for l in w:
        if out and out[-1][0] == l[0] and out[-1][1] == -l[1]:
            out.pop()
        else:
            out.append(l)
    return tuple(out)

def act(aut, w):
    """perm and sections of a word (letters applied right to left)."""
    d = len(next(iter(aut.values()))[0])
    perm = list(range(d)); secs = [() for _ in range(d)]
    for (g, e) in reversed(w):
        p, s = letter(aut, g, e)
        secs = [s[perm[x]] + secs[x] for x in range(d)]
        perm = [p[perm[x]] for x in range(d)]
    return tuple(perm), [reduce(s) for s in secs]

def part_a():
    print('== A. section-invariant characters (dimension of solution space over Q)')
    for name, aut in A.items():
        gens = sorted(aut); n = len(gens); rows = []
        for g in gens:
            r = [0] * n; r[gens.index(g)] += 1
            for s in aut[g][1]:
                for (h, e) in s:
                    r[gens.index(h)] -= e
            rows.append(r)
        for g in INVOL.get(name, ''):
            r = [0] * n; r[gens.index(g)] = 2; rows.append(r)
        for w in EXTRA.get(name, []):
            r = [0] * n
            for (h, e) in w:
                r[gens.index(h)] += e
            rows.append(r)
        ns = Matrix(rows).nullspace()
        print(f'{name}: gens {gens}, dim = {len(ns)}, basis = {[list(v) for v in ns]}')

def trivial(aut, w, memo, stack):
    w = reduce(w)
    if not w:
        return True
    if w in memo:
        return memo[w]
    if w in stack:
        return True  # greatest fixed point
    perm, secs = act(aut, w)
    if perm != tuple(range(len(perm))):
        memo[w] = False; return False
    stack.add(w)
    res = all(trivial(aut, s, memo, stack) for s in secs)
    stack.discard(w)
    memo[w] = res
    return res

def part_b(L):
    print(f'== B. trivial reduced words of length <= {L} have psi = 0')
    for name, psi in [('basilica', {'a': 1, 'b': 1}), ('odometer', {'a': 1})]:
        aut = A[name]; gens = sorted(aut); memo = {}
        letters = [(g, e) for g in gens for e in (1, -1)]
        ntriv = bad = 0
        for n in range(1, L + 1):
            for w in itertools.product(letters, repeat=n):
                if reduce(w) != w:
                    continue
                if trivial(aut, w, memo, set()):
                    ntriv += 1
                    if sum(psi[g] * e for (g, e) in w) != 0:
                        bad += 1
        print(f'{name}: psi = {psi}; nonempty trivial reduced words: {ntriv}; with psi != 0: {bad}')
        assert bad == 0
    # the shortest trivial words are printed, to show the check is not vacuous
    aut = A['basilica']; memo = {}; ex = []
    letters = [(g, e) for g in 'ab' for e in (1, -1)]
    for n in range(1, 13):
        for w in itertools.product(letters, repeat=n):
            if reduce(w) == w and trivial(aut, w, memo, set()):
                ex.append(''.join(g if e == 1 else g.upper() for g, e in w))
        if ex:
            break
    print('basilica: shortest nonempty trivial reduced words (A = a^-1, B = b^-1):', ex[:6], 'total', len(ex))

def rank(M):
    return M.rank()

def part_c(trials):
    print(f'== C. Koszul lemma on {trials} random commuting pairs (A, p(A)) over Q')
    random.seed(7); seen = {}
    for _ in range(trials):
        n = random.randint(2, 4)
        Am = Matrix(n, n, lambda i, j: random.randint(0, 3))
        c = [random.randint(-2, 2) for _ in range(3)]
        Bm = c[0] * eye(n) + c[1] * Am + c[2] * Am * Am
        N1, N2 = eye(n) - Am, eye(n) - Bm
        h0 = n - rank(N1.row_join(N2))
        h2 = n - rank(N1.col_join(N2))
        h1 = h0 + h2  # Euler characteristic of the Koszul complex is 0
        key = (h0 == 0, h2 == 0)
        seen[key] = seen.get(key, 0) + 1
        assert not (h0 == 0 and h2 != 0)
    print('counts of (H0==0, H2==0):', seen, '-> H0 = 0 always forces H2 = 0 = H1')

def part_d():
    print('== D. 1 - Phi on H_ab (x) Q for the basilica, basis a, b')
    Phi = Matrix([[0, 1], [1, 0]])
    M = eye(2) - Phi
    print('1 - Phi =', M.tolist(), '; rank', M.rank(), '-> coker rank', 2 - M.rank())

if __name__ == '__main__':
    part_a(); part_b(8); part_c(400); part_d()
    print('ALL OK')
