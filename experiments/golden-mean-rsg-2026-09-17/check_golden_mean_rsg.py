"""Sanity checks for research/golden-mean-periodic-group-lies-in-a-contracting-rsg.md.

Maps act on finite binary words over {'1','2'} (prefixes of points of X^omega);
each returns the determined output prefix.  Generators follow Nekrashevych,
arXiv:1601.01033, Section 7 (TeX lines 1405-1428).

Checks (pointwise, on random samples; the proof in the node is by hand):
 (1) b0, c0, d0 are involutions and b0 c0 = d0 (K is a Klein four group);
 (2) every sampled element g of F (random words in the 12 generators) has, at
     every sampled deep cone C_alpha, a local action in the 7-element set
     N0 = {id, b0, c0, d0, b0|_1, c0|_1, d0|_1}.
"""
import random

NEXT = {'b': 'c', 'c': 'd', 'd': 'b'}


def kappa(s, w):
    """State s in {'b','c','d','1'} applied to the finite word w."""
    out = []
    i = 0
    while True:
        if s == '1':
            out.append(w[i:])
            break
        if i >= len(w):
            break
        if w[i] == '2':
            out.append('11' if s in 'bc' else '2')
            i += 1
        elif i + 1 >= len(w):
            break
        elif w[i + 1] == '1':  # prefix 11
            out.append('2' if s in 'bc' else '11')
            i += 2
        else:  # prefix 12
            out.append('12')
            i += 2
            s = NEXT[s]
    return ''.join(out)


def a0(w):
    if w.startswith('11'):
        return '2' + w[2:]
    if w.startswith('2'):
        return '11' + w[1:]
    return w


def x0(x, w):
    return a0(w) if x == 'a' else kappa(x, w)


def gen(name):
    x, i = name[0], int(name[1])
    if i == 0:
        return lambda w: x0(x, w)
    if i == 1:
        return lambda w: ('1' + x0(x, w[1:])) if w.startswith('1') else w
    return lambda w: ('2' + x0(x, w[1:])) if w.startswith('2') else w


GENS = [x + str(i) for x in 'abcd' for i in range(3)]


def rand_word(n, rng):
    return ''.join(rng.choice('12') for _ in range(n))


def gcp(words):
    beta = min(words, key=len)
    for x in words:
        j = 0
        while j < len(beta) and x[j] == beta[j]:
            j += 1
        beta = beta[:j]
    return beta


def main():
    rng = random.Random(20260917)
    L = 400
    for trial in range(2000):
        w = rand_word(L, rng) if trial % 2 else '12' * rng.randint(0, 150) + rand_word(L, rng)
        for s in 'bcd':
            ww = kappa(s, kappa(s, w))
            assert len(ww) > L - 20 and w.startswith(ww), s
        bc = kappa('b', kappa('c', w))
        d = kappa('d', w)
        m = min(len(bc), len(d))
        assert m > L - 20 and bc[:m] == d[:m]
    print('(1) K = {1,b0,c0,d0} is a Klein four group on 2000 samples: OK')

    cands = [('id', None, None)]
    for s in 'bcd':
        cands.append((s, '', s))
        cands.append((s + '|1', '1', s))
    tests = bad = 0
    found = set()
    for trial in range(400):
        word = [rng.choice(GENS) for _ in range(rng.randint(1, 16))]
        fs = [gen(n) for n in word]

        def g(w):
            for f in fs:
                w = f(w)
            return w
        for _ in range(5):
            k = rng.randint(12, 30)
            alpha = rng.choice(['12' * k, '12' * k + '1', '1' + '12' * k,
                                '2' + '12' * k, '11' + '12' * k, rand_word(40, rng)])
            samples = [rand_word(L, rng) for _ in range(80)]
            imgs = [g(alpha + w) for w in samples]
            beta = gcp(imgs)
            loc = [x[len(beta):] for x in imgs]
            ok = False
            for name, t, s in cands:
                if s is None:
                    zs = samples
                else:
                    zs = [kappa(s, t + w) for w in samples]
                    zs = [z[len(gcp(zs)):] for z in zs]
                good = True
                for z, y in zip(zs, loc):
                    n = min(len(z), len(y)) - 5
                    if n < 100 or z[:n] != y[:n]:
                        good = False
                        break
                if good:
                    ok = True
                    found.add(name)
                    break
            tests += 1
            bad += (not ok)
    print('(2) deep local actions tested: %d, outside N0: %d; N0 members seen: %s'
          % (tests, bad, sorted(found)))
    assert bad == 0


if __name__ == '__main__':
    main()
