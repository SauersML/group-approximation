"""Sanity checks for corridor_lb.py.

1. Lee's relators are trivial in H_3 (independent point-function implementation).
2. w_m is trivial in H_3.
3. Soundness test: for words that are products of k conjugates of relators (so
   Area <= k), the corridor bound sum_inv_min must be <= k.
4. Brute-force check of the matching DP on small words.
"""
import random
import itertools
from corridor_lb import lower_bound, inv_word, comm, pw


def lam(x, y):
    def f(pt):
        r, p = pt
        if r == x:
            return (x, p - 1) if p >= 1 else (y, 0)
        if r == y:
            return (y, p + 1)
        return pt
    return f


def lami(x, y):
    return lam(y, x)


LET = {'X': lam(1, 2), 'x': lami(1, 2), 'Y': lam(1, 3), 'y': lami(1, 3),
       'a': lambda pt: (1, 1) if pt == (1, 0) else ((1, 0) if pt == (1, 1) else pt)}


def act(word, pt):
    for c in word:
        pt = LET[c](pt)
    return pt


def is_trivial(word, D=None):
    D = D or len(word) + 5
    return all(act(word, (r, p)) == (r, p) for r in (1, 2, 3) for p in range(D))


def conj(u, g):  # g^u = u^-1 g u
    return inv_word(u) + g + u


RELS = ['aa', ('a' + conj('X', 'a')) * 3, comm('a', conj('XX', 'a')),
        'XYxy' + 'a', conj('x', 'a') + inv_word(conj('y', 'a')),
        # HNN relators of the presentation used in the hand proof
        'YXy' + inv_word('aX'), 'Yay' + inv_word('Xax')]

if __name__ == '__main__':
    for r in RELS:
        assert is_trivial(r), r
    print('relators trivial: ok')
    for m in range(1, 7):
        s = pw('X', m) + pw('Y', m) + pw('x', m) + pw('y', m)
        z = pw('xY', m)
        w = s + z + inv_word(s) + inv_word(z)
        assert is_trivial(w), m
    print('w_m trivial: ok')
    random.seed(1)
    worst = 0
    for trial in range(300):
        k = random.randint(1, 4)
        w = ''
        for _ in range(k):
            u = ''.join(random.choice('XxYya') for _ in range(random.randint(0, 25)))
            r = random.choice(RELS)
            if random.random() < 0.5:
                r = inv_word(r)
            w += inv_word(u) + r + u
        lb, _ = lower_bound(w)
        assert lb <= k, (w, lb, k)   # Area <= k and Area >= sum inv
        worst = max(worst, lb / k)
    print('soundness on products of relator conjugates: ok, max sum_inv per relator', worst)
    # brute-force DP check
    for m in (1, 2):
        s = pw('X', m) + pw('Y', m) + pw('x', m) + pw('y', m)
        z = pw('xY', m)
        w = s + z + inv_word(s) + inv_word(z)
        lb, cost = lower_bound(w)
        K = sum(1 for c in w if c in 'Yy')
        best = float('inf')

        def rec(items, acc):
            global best
            if not items:
                best = min(best, acc)
                return
            s0 = items[0]
            for idx in range(1, len(items)):
                t0 = items[idx]
                c = cost.get((s0, t0))
                if c is None:
                    continue
                inside = items[1:idx]
                outside = items[idx + 1:]
                # non-crossing: inside and outside matched separately
                sub_best_before = best
                rec_pair(inside, outside, acc + c)

        def rec_pair(inside, outside, acc):
            global best
            b_in = solve(tuple(inside))
            b_out = solve(tuple(outside))
            best = min(best, acc + b_in + b_out)

        memo = {}

        def solve(items):
            if items in memo:
                return memo[items]
            if not items:
                return 0
            res = float('inf')
            for idx in range(1, len(items)):
                c = cost.get((items[0], items[idx]))
                if c is None:
                    continue
                res = min(res, c + solve(items[1:idx]) + solve(items[idx + 1:]))
            memo[items] = res
            return res
        # exhaustive over all perfect matchings, filtering non-crossing
        def all_match(items):
            if not items:
                yield []
                return
            a = items[0]
            for i in range(1, len(items)):
                rest = items[1:i] + items[i + 1:]
                for mm in all_match(rest):
                    yield [(a, items[i])] + mm
        def crossing(M):
            for (p, q), (r, s2) in itertools.combinations(M, 2):
                if (p < r < q < s2) or (r < p < s2 < q):
                    return True
            return False
        ex = float('inf')
        for M in all_match(list(range(K))):
            if crossing(M):
                continue
            if all((min(p, q), max(p, q)) in cost for p, q in M):
                ex = min(ex, sum(cost[(min(p, q), max(p, q))] for p, q in M))
        print('m', m, 'dp', lb, 'exhaustive', ex)
        assert ex == lb
