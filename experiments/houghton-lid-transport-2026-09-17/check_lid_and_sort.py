"""Permutation-arithmetic checks for
research/houghton-ray-stabilizer-corridors-cap-quadratic-for-n-ge-4.md.

Model of H_n: points (r, q), r in 1..n, q >= 1.  Permutations act on the
right, a word is applied letter by letter from left to right.
  ('L', a, b)  = lambda_(a,b): (a,1)->(b,1), (a,q)->(a,q-1) q>=2, (b,q)->(b,q+1)
                 (pop the top of stack a, push it onto stack b); its inverse
                 is ('L', b, a).
  ('S', p, p') = the transposition of the points p, p'.
Y = lambda_(1,n), K = pointwise stabilizer of ray n (= H_(n-1) on rays 1..n-1),
phi(h) = Y h Y^-1, so phi^k(h) = Y^k h Y^-k.

Two words are equal in H_n iff they have the same eventual translations and
agree on every point of depth <= M, where M exceeds the depth range touched
by either word (a deeper point only ever sees translations).

Checks:
 (1) phi maps the generators lambda_(a,b) (a, b < n) and alpha into K.
 (2) Lid lemma: for finitary sigma in K supported in depth <= D and k >= 0,
     phi^k(sigma) = z^-1 sigma z with z = L(r,p)^D L(r,1)^k L(p,r)^D.
 (3) phi^k(L(1,j)^a) = L(r,1)^-k L(1,j)^a L(r,1)^k for r not in {1, j}.
 (4) Stack merge sort: every finitary sigma of K supported in depth <= D is
     a word in the lambda_(a,b), a,b < n, of length <= C D log D (n-1 >= 3).
 (5) Forced matching for [Y^m u Y^-m, alpha], u a random K-word: the only
     admissible opposite-sign pairs are a_i-b_(m+1-i), c_i-d_(m+1-i) and
     b_m-c_1, with arcs phi^k(u^-1), phi^k(u).
"""
import math
import random

random.seed(20260917)


def inv(w):
    out = []
    for t in reversed(w):
        if t[0] == 'L':
            out.append(('L', t[2], t[1]))
        else:
            out.append(t)
    return out


def act(p, w):
    r, q = p
    for t in w:
        if t[0] == 'L':
            a, b = t[1], t[2]
            if r == a:
                if q == 1:
                    r, q = b, 1
                else:
                    q -= 1
            elif r == b:
                q += 1
        else:
            if (r, q) == t[1]:
                r, q = t[2]
            elif (r, q) == t[2]:
                r, q = t[1]
    return (r, q)


def trans(w, n):
    v = [0] * (n + 1)
    for t in w:
        if t[0] == 'L':
            v[t[1]] -= 1
            v[t[2]] += 1
    return v


def depth(w):
    d = 0
    for t in w:
        if t[0] == 'S':
            d = max(d, t[1][1], t[2][1])
    return d


def equal(w1, w2, n):
    if trans(w1, n) != trans(w2, n):
        return False
    M = len(w1) + len(w2) + depth(w1) + depth(w2) + 5
    return all(act((r, q), w1) == act((r, q), w2)
               for r in range(1, n + 1) for q in range(1, M + 1))


def fixes_ray(w, n, ray):
    M = len(w) + depth(w) + 5
    if trans(w, n)[ray] != 0:
        return False
    return all(act((ray, q), w) == (ray, q) for q in range(1, M + 1))


def pw(t, e):
    return [t] * e if e >= 0 else inv([t]) * (-e)


def rand_finitary(n, D, moves):
    """Random finitary permutation of rays 1..n-1 inside depth <= D."""
    pts = [(r, q) for r in range(1, n) for q in range(1, D + 1)]
    return [('S',) + tuple(random.sample(pts, 2)) for _ in range(moves)]


ALPHA = ('S', (1, 1), (1, 2))


def check_hnn(n):
    Y = [('L', 1, n)]
    gens = [[('L', a, b)] for a in range(1, n) for b in range(1, n) if a != b]
    gens.append([ALPHA])
    for g in gens:
        assert fixes_ray(Y + g + inv(Y), n, n), (n, g)
    print('n=%d (1) phi(K generators) fix ray n: ok (%d generators)' % (n, len(gens)))


def check_lid(n, trials=40):
    r, p = 2, 3
    for _ in range(trials):
        D = random.randint(1, 7)
        k = random.randint(0, 9)
        s = rand_finitary(n, D, random.randint(1, 12))
        lhs = pw(('L', 1, n), k) + s + pw(('L', 1, n), -k)
        z = pw(('L', r, p), D) + pw(('L', r, 1), k) + pw(('L', p, r), D)
        assert equal(lhs, inv(z) + s + z, n), (n, D, k, s)
    print('n=%d (2) lid lemma phi^k(sigma) = z^-1 sigma z: ok (%d trials)' % (n, trials))


def check_translations(n):
    cnt = 0
    for j in range(2, n):
        for r in range(2, n):
            if r == j:
                continue
            for a in range(-4, 5):
                for k in range(0, 7):
                    lhs = pw(('L', 1, n), k) + pw(('L', 1, j), a) + pw(('L', 1, n), -k)
                    rhs = pw(('L', r, 1), -k) + pw(('L', 1, j), a) + pw(('L', r, 1), k)
                    assert equal(lhs, rhs, n), (n, j, r, a, k)
                    cnt += 1
    print('n=%d (3) phi^k(L(1,j)^a) = L(r,1)^-k L(1,j)^a L(r,1)^k: ok (%d cases)' % (n, cnt))


def stack_sort_word(n, keys):
    """keys[i] = target depth of the item at (1, i+1).  Returns a word in the
    lambda_(a,b), a, b in {1,2,3}, that puts key 1 on top of ray 1, key 2
    below it, ... (merge sort with three stacks), touching nothing else."""
    st = {1: list(reversed(keys)), 2: [], 3: []}   # top of stack = end of list
    word = []

    def mv(a, b):
        st[b].append(st[a].pop())
        word.append(('L', a, b))

    def srt(s, N, t, u):
        if N <= 1:
            return
        h = N // 2
        for _ in range(h):
            mv(s, t)
        srt(t, h, s, u)
        srt(s, N - h, t, u)
        cs, ct = N - h, h
        for _ in range(N):
            if cs and (not ct or st[s][-1] < st[t][-1]):
                mv(s, u)
                cs -= 1
            else:
                mv(t, u)
                ct -= 1
        for _ in range(N):
            mv(u, s)

    srt(1, len(keys), 2, 3)
    assert st[1] == list(reversed(sorted(keys))) and not st[2] and not st[3]
    return word


def realize(n, D, sigma):
    """Word in lambda_(a,b), a, b < n, equal to the finitary sigma (depth <= D)."""
    G = []
    for r in range(2, n):
        G += pw(('L', r, 1), D)
    N = (n - 1) * D
    Gi = inv(G)
    keys = []
    for i in range(1, N + 1):
        p = act((1, i), Gi)
        tgt = act(act(p, sigma), G)
        assert tgt[0] == 1 and tgt[1] <= N
        keys.append(tgt[1])
    S = stack_sort_word(n, keys)
    return G + S + Gi


def check_sort(n, Ds=(1, 2, 3, 5, 8, 13, 21, 34)):
    worst = 0.0
    for D in Ds:
        for _ in range(3):
            s = rand_finitary(n, D, 4 * n * D)
            W = realize(n, D, s)
            assert equal(W, s, n), (n, D)
            ratio = len(W) / (D * max(1.0, math.log2(D)))
            worst = max(worst, ratio)
        print('n=%d (4) D=%2d  |word| = %6d   |word|/(D log2 D) = %.1f'
              % (n, D, len(W), len(W) / (D * max(1.0, math.log2(D)))))
    print('n=%d (4) stack merge sort realizes sigma: ok (max ratio %.1f)' % (n, worst))


def check_forced(n, ms=(2, 3, 4, 5)):
    kgens = [('L', a, b) for a in range(1, n) for b in range(1, n) if a != b] + [ALPHA]
    Y, y = ('L', 1, n), ('L', n, 1)
    for m in ms:
        for _ in range(5):
            u = [random.choice(kgens) for _ in range(random.randint(1, 8))]
            W = [Y] * m + inv(u) + [y] * m + [ALPHA] + [Y] * m + u + [y] * m + [ALPHA]
            assert equal(W, [], n)
            pos = [i for i, t in enumerate(W) if t in (Y, y)]
            name = {}
            for idx, i in enumerate(pos):
                blk, j = divmod(idx, m)
                name[i] = ('abcd'[blk], j + 1)
            adm = set()
            for x in range(len(pos)):
                for z in range(x + 1, len(pos)):
                    i, j = pos[x], pos[z]
                    if W[i] == W[j]:
                        continue
                    if fixes_ray(W[i + 1:j], n, n):
                        adm.add((name[i], name[j]))
            exp = {(('a', i), ('b', m + 1 - i)) for i in range(1, m + 1)}
            exp |= {(('c', i), ('d', m + 1 - i)) for i in range(1, m + 1)}
            exp.add((('b', m), ('c', 1)))
            assert adm == exp, (n, m, u, sorted(adm - exp), sorted(exp - adm))
    print('n=%d (5) forced matching for [Y^m u Y^-m, alpha], random u: ok' % n)


if __name__ == '__main__':
    for n in (4, 5):
        check_hnn(n)
        check_lid(n)
        check_translations(n)
        check_forced(n)
        check_sort(n)
