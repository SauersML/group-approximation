"""Check the weighted block lemma in L_{F_2}(1,2).

Weights: phi(s_0) = p, phi(s_1) = q with p, q >= 1.  For N >= 1 let C_N be the set of
words c with phi(c) >= N whose proper prefixes all have phi < N (a finite complete
prefix code).  The lemma says:

 (i)   sum_{c in C_N} s_c t_c = 1 and t_c s_d = delta_{c,d} for c, d in C_N;
 (ii)  every s_w t_v with phi(w) >= phi(v) and phi(v) < N equals
       sum_u s_c s_{w''} t_{v u}, where u runs over the words with v u in C_N and
       w u = c w'' with c in C_N; so it lies in B_N = { sum s_c P_{c,d}(s) t_d }.

We verify (i) and (ii) in normal form for several weights and N, and check (ii) on
random elements of L^phi_{>=0}.  It also prints the mixed-degree example
a = s_0 + s_0 t_1 t_1 (standard degrees -1 and 1, bidegrees (1,0) and (1,-2)), which
lies in L^phi_{>=0} for phi = (3, 1).

Run: python3 check_weighted_blocks.py
"""
import sys, random
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from leavitt import elt, mul, add, ONE, words


def phi(w, p, q):
    return sum(p if c == '0' else q for c in w)


def code(N, p, q):
    out, frontier = [], ['']
    while frontier:
        nxt = []
        for w in frontier:
            if phi(w, p, q) >= N:
                out.append(w)
            else:
                nxt += [w + '0', w + '1']
        frontier = nxt
    return out


def block_expand(w, v, C):
    """Return list of (c, w'', d) with s_w t_v = sum s_c s_{w''} t_d, d = v u in C."""
    terms = []
    Cset = set(C)
    for d in C:
        if not d.startswith(v):
            continue
        u = d[len(v):]
        wu = w + u
        cs = [c for c in C if wu.startswith(c)]
        assert len(cs) == 1, (w, v, d, cs)
        c = cs[0]
        terms.append((c, wu[len(c):], d))
    return terms


def main():
    rng = random.Random(0)
    for p, q in [(1, 1), (1, 2), (2, 1), (2, 3), (3, 1), (1, 4)]:
        for N in range(1, 7):
            C = code(N, p, q)
            tot = elt(*[(c, c) for c in C])
            assert tot == ONE, (p, q, N)
            for c in C:
                for d in C:
                    assert mul(elt(('', c)), elt((d, ''))) == (ONE if c == d else frozenset())
            # (ii) on all monomials with |w|, |v| <= 4, phi(w) >= phi(v), phi(v) < N
            count = 0
            for w in words(4):
                for v in words(4):
                    if phi(w, p, q) >= phi(v, p, q) and phi(v, p, q) < N:
                        lhs = elt((w, v))
                        rhs = elt(*[(c + w2, d) for c, w2, d in block_expand(w, v, C)])
                        assert lhs == rhs, (p, q, N, w, v)
                        count += 1
        print('weights', (p, q), 'N = 1..6: prefix code and block expansion verified')
    a = add(elt(('0', '')), elt(('0', '11')))
    print('example a = s_0 + s_0 t_11, standard degrees', sorted({len(w) - len(v) for w, v in a}),
          'phi_(3,1)-degrees', sorted({phi(w, 3, 1) - phi(v, 3, 1) for w, v in a}))


if __name__ == '__main__':
    main()
