"""Labelled coset chains over K = <a, b a b^-1 b^-1> in L = F(a, b).

R_n(h_1..h_n) = #{(k_1..k_n) in K^n : h_n k_n ... h_1 k_1 in K b}
             = number of class sequences K = x_0 -> x_1 -> ... -> x_n = Kb
               with x_i = K h_i k x_{i-1} (one point of x_{i-1} per step).
Right cosets Kg are read from the base 0 of the Schreier graph of K.
Letters: a, A = a^-1, b, B = b^-1.  K-syllables are truncated at length L;
counts are reported for increasing L to check stabilisation.
"""
INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def red(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return ''.join(out)


def inv(w):
    return ''.join(INV[x] for x in reversed(w))


# core of the Schreier graph of K: directed labelled edges u -x-> v
CORE = [(0, 'a', 0), (0, 'b', 1), (1, 'a', 2), (1, 'b', 2)]
STEP = {}
for _u, _x, _v in CORE:
    STEP[(_u, _x)] = _v
    STEP[(_v, INV[_x])] = _u
PATH = {0: '', 1: 'b', 2: 'ba'}


def cls(g):
    """class id of Kg: (core vertex, hanging suffix)."""
    g = red(g)
    v = 0
    for i, x in enumerate(g):
        if (v, x) in STEP:
            v = STEP[(v, x)]
        else:
            return (v, g[i:])
    return (v, '')


def rep(c):
    return red(PATH[c[0]] + c[1])


def in_K(g):
    return cls(g) == (0, '')


def k_elements(L):
    """reduced words of K of length <= L (closed non-backtracking core paths at 0)."""
    out = {''}
    stack = [(0, '')]
    while stack:
        v, w = stack.pop()
        if len(w) == L:
            continue
        for x in 'aAbB':
            if w and w[-1] == INV[x]:
                continue
            if (v, x) in STEP:
                u = STEP[(v, x)]
                ww = w + x
                if u == 0:
                    out.add(ww)
                stack.append((u, ww))
    return sorted(out, key=len)


def step(counts, h, KL):
    new = {}
    for c, m in counts.items():
        g = rep(c)
        for k in KL:
            d = cls(h + k + g)
            new[d] = new.get(d, 0) + m
    return new


def R(labels, KL, split=None, target='b'):
    """number of labelled chains from K to K*target."""
    n = len(labels)
    if split is None:
        split = (n + 1) // 2
    F = {cls(''): 1}
    for h in labels[:split]:
        F = step(F, h, KL)
    B = {cls(target): 1}
    for h in reversed(labels[split:]):
        B = step(B, inv(h), KL)
    return sum(m * B.get(c, 0) for c, m in F.items())


def reduced_words(n):
    out = ['']
    for _ in range(n):
        out = [w + x for w in out for x in 'aAbB' if not (w and w[-1] == INV[x])]
    return out


def step_nb(states, h, hprev, KL):
    """non-backtracking step; states map (prev, cur) -> count."""
    new = {}
    back = hprev is not None and red(h + hprev) == ''
    for (p, c), m in states.items():
        g = rep(c)
        for k in KL:
            d = cls(h + k + g)
            if back and d == p:
                continue
            key = (c, d)
            new[key] = new.get(key, 0) + m
    return new


def R_nb(labels, KL, split=None, target='b'):
    """labelled chains K -> K*target with no immediate reversal of a pair."""
    n = len(labels)
    if split is None:
        split = (n + 1) // 2
    F = {(None, cls('')): 1}
    prev = None
    for h in labels[:split]:
        F = step_nb(F, h, prev, KL)
        prev = h
    if split == n:
        return sum(m for (p, c), m in F.items() if c == cls(target))
    B = {(None, cls(target)): 1}
    prevb = None
    for h in reversed(labels[split:]):
        B = step_nb(B, inv(h), prevb, KL)
        prevb = inv(h)
    hs, hn = labels[split - 1], labels[split]
    back = red(hs + hn) == ''
    Bc = {}
    for (q, c), m in B.items():
        Bc.setdefault(c, []).append((q, m))
    tot = 0
    for (p, c), m in F.items():
        for q, mb in Bc.get(c, ()):
            if back and p == q:
                continue
            tot += m * mb
    return tot


if __name__ == '__main__':
    for L in (4, 8, 12, 16):
        print(L, len(k_elements(L)))
