"""Chord-cell bootstrap versus the 2-of-3 seed closure, for L = F(a, b),
K = <a, c>, c = b a b^-2.  Companion to
research/fpbs-mal-bootstrap-certified-chords-pay-seed-floor.md.

Part 1 (exact, free group): the graphing {bab, bbab} generates L over K,
both labels have double-coset b-length 2, so its bootstrap closure from the
empty set is empty although generation holds.

Part 2 (finite actions, combinatorial lemma): on random finite actions of
L (random permutations a, b of N points) with a sprinkle A0 of b-seeds and
random chords of arbitrary length, run the bootstrap closure with rules
  (T) 2-of-3 on (w, a w, b w);
  (C) for each chord instance, if all but one of its path b-edges are known,
      add the last one,
charge each (C)-firing to its chord instance, and check
  (i)  |A0| + #charged <= |A0| + #chords;
  (ii) the plain 2-of-3 closure of A0 + charged points contains the whole
       bootstrap closure.
The lemma uses no freeness, so finite actions are a valid test bed.
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-chord-unfolding-2026-09-17'))
from coset_b_length import b_length, red, inv  # noqa: E402


def part1():
    h1, h2 = 'bab', 'bbab'
    print('Part 1: |%s| = %d, |%s| = %d' % (h1, b_length(h1), h2, b_length(h2)))
    print('  red(h2 * h1^-1) =', red(h2 + inv(h1)))
    print('  so <K, h1, h2> contains b, and {h1|X, h2|X} generates R_L over R_K;')
    print('  every label has b-length >= 2, so (C) needs one known edge and (T)')
    print('  needs two: the bootstrap closure of the empty set is empty.')


def perm(n, rng):
    p = list(range(n))
    rng.shuffle(p)
    q = [0] * n
    for i, j in enumerate(p):
        q[j] = i
    return p, q


def path_seeds(word, x, A, Ai, B, Bi):
    """Seeds (points z whose b-edge (z, bz) is used) along word applied to x,
    word read right to left as a left action."""
    seeds = []
    p = x
    for ch in reversed(word):
        if ch == 'a':
            p = A[p]
        elif ch == 'A':
            p = Ai[p]
        elif ch == 'b':
            seeds.append(p)
            p = B[p]
        else:
            p = Bi[p]
            seeds.append(p)
    return seeds


def closure23(S, n, A, B):
    S = set(S)
    changed = True
    while changed:
        changed = False
        for w in range(n):
            t = (w, A[w], B[w])
            if sum(1 for z in t if z in S) >= 2:
                for z in t:
                    if z not in S:
                        S.add(z)
                        changed = True
    return S


def bootstrap(S0, chords, n, A, B):
    S = set(S0)
    charged = set()
    fired = [False] * len(chords)
    changed = True
    while changed:
        changed = False
        add = set()
        for w in range(n):
            t = (w, A[w], B[w])
            if sum(1 for z in t if z in S) >= 2:
                add.update(z for z in t if z not in S)
        for k, seeds in enumerate(chords):
            if fired[k]:
                continue
            unk = [z for z in set(seeds) if z not in S]
            if len(unk) == 1:
                add.add(unk[0])
                charged.add(unk[0])
                fired[k] = True
            elif not unk:
                fired[k] = True
        if add - S:
            S |= add
            changed = True
    return S, charged, sum(fired)


def rand_word(rng, lo, hi):
    L = rng.randint(lo, hi)
    w = ''
    while len(w) < L:
        ch = rng.choice('aAbB')
        if w and inv(ch) == w[-1]:
            continue
        w += ch
    return w


def part2():
    print('Part 2: finite actions, N points, seed density q, chord density p')
    rng = random.Random(20260918)
    worst = 0.0
    for trial in range(12):
        n = 3000
        A, Ai = perm(n, rng)
        B, Bi = perm(n, rng)
        q = rng.choice([0.01, 0.03, 0.06, 0.10])
        p = rng.choice([0.02, 0.05, 0.10])
        lo, hi = rng.choice([(3, 6), (6, 12), (12, 24)])
        S0 = [z for z in range(n) if rng.random() < q]
        chords = []
        for x in range(n):
            if rng.random() < p:
                chords.append(path_seeds(rand_word(rng, lo, hi), x, A, Ai, B, Bi))
        S, charged, nf = bootstrap(S0, chords, n, A, B)
        seedset = set(S0) | charged
        C = closure23(seedset, n, A, B)
        ok_ii = S <= C
        ok_i = len(seedset) <= len(set(S0)) + len(chords)
        worst = max(worst, len(seedset) / max(1, len(set(S0)) + len(chords)))
        print('  q=%.2f p=%.2f len=%s |A0|=%4d chords=%4d fired=%4d charged=%4d'
              ' |boot|/N=%.3f |cl(A0+charged)|/N=%.3f  (i)%s (ii)%s'
              % (q, p, (lo, hi), len(set(S0)), len(chords), nf, len(charged),
                 len(S) / n, len(C) / n, ok_i, ok_ii))
        assert ok_i and ok_ii
    print('  all checks passed; max |A0+charged| / (|A0|+#chords) = %.3f' % worst)


if __name__ == '__main__':
    part1()
    part2()
