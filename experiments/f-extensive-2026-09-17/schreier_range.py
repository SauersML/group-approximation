"""Range of simple random walk on orbit Schreier graphs of Thompson's F (Cantor model).

A point is a finite prefix p followed by the tail t[n:], where t is a fixed infinite word.
Canonical form strips p[-1] == t[n-1]. Orbits are tail-equivalence classes.
Generators (acting on leading bits):
  x0: 00s->0s, 01s->10s, 1s->11s
  x1: 0s->0s, 1s -> 1 x0(s)
R_n / n -> 0 for recurrent graphs; R_n / n -> positive escape probability if transient
(Kesten-Spitzer-Whitman for transitive graphs; for general graphs R_n/n>0 a.s. limit
positive still certifies transience along the sample).
Usage: python3 schreier_range.py STEPS TRIALS
"""
import random
import sys


class Tail:
    def __init__(self, kind, seed):
        self.kind = kind
        self.bits = []
        self.rng = random.Random(seed)
        if kind == 'golden':
            a, b = '0', '01'
            while len(b) < 1 << 21:
                a, b = b, b + a
            self.word = b

    def __getitem__(self, i):
        if self.kind == 'dyadic':
            return '0'
        if self.kind == 'golden':
            return self.word[i]
        while len(self.bits) <= i:
            self.bits.append('01'[self.rng.getrandbits(1)])
        return self.bits[i]


def canon(p, n, t):
    while p and n > 0 and p[-1] == t[n - 1]:
        p = p[:-1]
        n -= 1
    return p, n


def need(p, n, t, k):
    while len(p) < k:
        p += t[n]
        n += 1
    return p, n


def x0(p, n, t, inv):
    p, n = need(p, n, t, 2)
    if not inv:
        if p[:2] == '00':
            p = '0' + p[2:]
        elif p[:2] == '01':
            p = '10' + p[2:]
        else:
            p = '11' + p[1:]
    else:
        if p[0] == '0':
            p = '00' + p[1:]
        elif p[:2] == '10':
            p = '01' + p[2:]
        else:
            p = '1' + p[2:]
    return canon(p, n, t)


def x1(p, n, t, inv):
    p, n = need(p, n, t, 3)
    if p[0] == '0':
        return canon(p, n, t)
    q, m = x0(p[1:], n, t, inv)
    return canon('1' + q, m, t)


def walk(kind, steps, seed):
    t = Tail(kind, seed)
    rng = random.Random(seed + 7919)
    if kind == 'dyadic':
        p, n = '1', 0
    else:
        p, n = '', 0
    seen = {(p, n)}
    out = {}
    k = 1
    for s in range(1, steps + 1):
        g = rng.randrange(4)
        if g < 2:
            p, n = x0(p, n, t, g == 1)
        else:
            p, n = x1(p, n, t, g == 3)
        seen.add((p, n))
        if s == 1 << k:
            out[s] = len(seen) / s
            k += 1
    return out


def main():
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 65536
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    for kind in ('dyadic', 'random', 'golden'):
        acc = {}
        for tr in range(trials):
            for s, v in walk(kind, steps, 1000 + tr).items():
                acc[s] = acc.get(s, 0.0) + v / trials
        print(kind, ' '.join('%d:%.3f' % (s, v) for s, v in sorted(acc.items()) if s >= 256))


if __name__ == '__main__':
    main()
