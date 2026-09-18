"""BFS on the Schreier graph of Thompson's F acting on dyadic rationals in (0,1).

Generators act as prefix substitutions on binary expansions:
  x0: 0w -> 00w, 10w -> 01w, 11w -> 1w
  x1: 0w -> 0w, 1u -> 1 x0(u)
A dyadic y in (0,1) is stored as its finite expansion p (ending in '1'), y = 0.p.
We compute the Schreier distance from 1/2 = '1' to every dyadic of depth <= K
(BFS restricted to depth <= K + SLACK) and report the maximum distance per depth.
"""
import json, sys
from collections import deque

K = int(sys.argv[1]) if len(sys.argv) > 1 else 12
SLACK = int(sys.argv[2]) if len(sys.argv) > 2 else 4


def norm(s):
    s = s.rstrip('0')
    return s


def x0(s):
    t = s + '000'
    if t[0] == '0':
        return norm('0' + s)
    if t[:2] == '10':
        return norm('01' + t[2:])
    return norm('1' + t[2:])


def x0i(s):
    t = s + '000'
    if t[0] == '1':
        return norm('1' + s)
    if t[:2] == '01':
        return norm('10' + t[2:])
    return norm('0' + t[2:])


def x1(s):
    if s[0] == '0':
        return s
    return norm('1' + x0(s[1:]))


def x1i(s):
    if s[0] == '0':
        return s
    return norm('1' + x0i(s[1:]))


def val(s):
    from fractions import Fraction
    return sum(Fraction(int(c), 2 ** (i + 1)) for i, c in enumerate(s))


def check():
    from fractions import Fraction as Fr
    def X0(t):
        if t <= Fr(1, 2): return t / 2
        if t <= Fr(3, 4): return t - Fr(1, 4)
        return 2 * t - 1
    def X1(t):
        if t <= Fr(1, 2): return t
        return Fr(1, 2) + X0(2 * t - 1) / 2
    import itertools
    for d in range(1, 8):
        for bits in itertools.product('01', repeat=d - 1):
            s = ''.join(bits) + '1'
            assert val(x0(s)) == X0(val(s)), s
            assert val(x1(s)) == X1(val(s)), s
            assert x0i(x0(s)) == s and x0(x0i(s)) == s, s
            assert x1i(x1(s)) == s and x1(x1i(s)) == s, s
    return True


def main():
    assert check()
    dist = {'1': 0}
    q = deque(['1'])
    cap = K + SLACK
    while q:
        s = q.popleft()
        for f in (x0, x0i, x1, x1i):
            t = f(s)
            if t == '' or len(t) > cap:
                continue
            if t not in dist:
                dist[t] = dist[s] + 1
                q.append(t)
    out = {}
    for s, d in dist.items():
        k = len(s)
        if k <= K:
            out.setdefault(k, [0, 0])
            out[k][0] = max(out[k][0], d)
            out[k][1] += 1
    res = {str(k): {'max_dist': out[k][0], 'count': out[k][1], 'expected_count': 2 ** (k - 1)} for k in sorted(out)}
    print(json.dumps({'K': K, 'slack': SLACK, 'per_depth': res}, indent=1))


if __name__ == '__main__':
    main()
