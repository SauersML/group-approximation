#!/usr/bin/env python3
"""Max-private pivot test for Guba's S_(3,5) in the positive monoid M of Thompson's F.

M: generators x_0, x_1, ...; relations x_j x_i = x_i x_(j+1) for i < j.
Normal forms: nondecreasing index tuples. For a total order < on each degree layer of M,
w has maximal S-right-factor m_max(w) = max{ m : w = s m, s in S }.
If every m in M has at least two w in S m with m_max(w) = m, then |S Y| >= 2|Y|
for every finite Y (the private points are disjoint across m), so S is doubling.

This script (1) cross-checks the insertion / left-division formulas against the
rewriting system, and (2) for several natural orders reports the smallest m (by degree,
then letter bound) with fewer than two private points.
"""
import itertools, json, random, sys

S = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (1, 2), (1, 3), (2, 2), (2, 3)]


def normalize(word):
    """Rewrite x_j x_i -> x_i x_(j+1) (i < j) until nondecreasing."""
    w = list(word)
    changed = True
    while changed:
        changed = False
        for k in range(len(w) - 1):
            j, i = w[k], w[k + 1]
            if i < j:
                w[k], w[k + 1] = i, j + 1
                changed = True
    return tuple(w)


def insert(p, m):
    """Normal form of x_p * m by the insertion rule."""
    m = list(m)
    for k in range(len(m)):  # k is 0-based position; 1-based position k+1
        if m[k] >= p + k:
            return tuple(m[:k] + [p + k] + m[k:])
    return tuple(m + [p + len(m)])


def left_div(w, p):
    """Return m with x_p * m = w, or None."""
    # x_p m inserts value p+k at the least 0-based k with m[k] >= p+k, so in w the
    # inserted letter is at the least k with w[k]-k >= p, and it must satisfy w[k]-k == p.
    for k, v in enumerate(w):
        e = v - k
        if e < p:
            continue
        if e == p:
            m = w[:k] + w[k + 1:]
            return m if insert(p, m) == w else None
        return None
    return None


def s_mult(s, m):
    return insert(s[0], insert(s[1], m))


def factors(w):
    out = []
    for s in S:
        m1 = left_div(w, s[0])
        if m1 is None:
            continue
        m0 = left_div(m1, s[1])
        if m0 is None:
            continue
        if s_mult(s, m0) == w:
            out.append((s, m0))
    return out


def normal_forms(d, L):
    return list(itertools.combinations_with_replacement(range(L + 1), d))


ORDERS = {
    'lex': lambda m: m,
    'revlex': lambda m: tuple(reversed(m)),
    'sum_lex': lambda m: (sum(m), m),
    'sum_revlex': lambda m: (sum(m), tuple(reversed(m))),
    'colex_neg': lambda m: tuple(-x for x in reversed(m)),
    'lex_neg': lambda m: tuple(-x for x in m),
    'sum_neg_lex': lambda m: (-sum(m), m),
}


def check_formulas(trials=20000, seed=1):
    rnd = random.Random(seed)
    for _ in range(trials):
        d = rnd.randint(0, 6)
        m = tuple(sorted(rnd.randint(0, 8) for _ in range(d)))
        p = rnd.randint(0, 9)
        w = normalize((p,) + m)
        if insert(p, m) != w:
            return False, ('insert', p, m, w)
        if left_div(w, p) != m:
            return False, ('left_div', p, m, w)
        s = S[rnd.randrange(9)]
        if s_mult(s, m) != normalize(s + m):
            return False, ('s_mult', s, m)
    return True, None


def run(dmax, L):
    ok, info = check_formulas()
    res = {'formula_check': ok, 'formula_counterexample': info, 'orders': {}}
    if not ok:
        return res
    for name, key in ORDERS.items():
        first_fail = None
        min_private = None
        for d in range(0, dmax + 1):
            for m in normal_forms(d, L):
                priv = 0
                for s in S:
                    w = s_mult(s, m)
                    fs = factors(w)
                    mmax = max((mm for (_, mm) in fs), key=key)
                    if mmax == m:
                        priv += 1
                if min_private is None or priv < min_private[0]:
                    min_private = (priv, m)
                if priv < 2 and first_fail is None:
                    first_fail = {'m': m, 'private': priv}
            if first_fail is not None:
                break
        res['orders'][name] = {'first_fail': first_fail, 'min_private': min_private}
    return res


if __name__ == '__main__':
    dmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    print(json.dumps(run(dmax, L), indent=1, default=list))
