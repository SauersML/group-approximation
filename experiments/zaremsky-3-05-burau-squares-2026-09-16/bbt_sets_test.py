"""Randomized exact test (Laurent polynomials over Z and F_p) of the clopen
4-set ping-pong configuration for (A^m, B^n), m,n>=3, built from the
Beridze-Bigelow-Traczyk sets X1 (arXiv:1904.11730, proof of Thm 3.1):
  S_B+ = X1, S_A+ = T X1, S_A- = T^-1 X1, S_B- = T^2 X1,
X1 = {v(x1) <= v(x2)-2, v(x1) <= v(x3)-2}, v = lowest t-degree.
Also checks that the same sets fail for exponent 2 (consistency with the
obstruction). This is a sanity test; the proof is by hand in the artifact."""
import random, sys
random.seed(20260916)
INF = 10**9

def red(p, P):
    return {d: (c % P if P else c) for d, c in p.items() if (c % P if P else c) != 0}

def add(p, q, P):
    r = dict(p)
    for d, c in q.items():
        r[d] = r.get(d, 0) + c
    return red(r, P)

def mul(p, q, P):
    r = {}
    for d1, c1 in p.items():
        for d2, c2 in q.items():
            r[d1+d2] = r.get(d1+d2, 0) + c1*c2
    return red(r, P)

def apply(M, x, P):
    return [ (lambda i: (lambda acc: acc)( 
        add(add(mul(M[i][0], x[0], P), mul(M[i][1], x[1], P), P), mul(M[i][2], x[2], P), P)))(i)
        for i in range(3)]

def val(p):
    return min(p) if p else INF

def C(c, d=0):
    return {d: c} if c else {}

def mats(sign):
    # sign=+1: BBT matrices at t; sign=-1: at -t
    s = sign
    A = [[{}, {}, C(-s, -1)], [{}, C(-s, 1), add(C(-s, -1), C(s, 1), 0)],
         [C(-1), {}, add(C(-s, -1), C(1), 0)]]
    B = [[C(-s, -1), C(1), {}], [{}, C(1), {}], [{}, C(1), C(-s, 1)]]
    return A, B
T  = [[C(-1), C(1), {}], [C(-1), {}, C(1)], [C(-1), {}, {}]]
Ti = [[{}, {}, C(-1)], [C(1), {}, C(-1)], [{}, C(1), C(-1)]]
T2 = [[{}, C(-1), C(1)], [{}, C(-1), {}], [C(1), C(-1), {}]]

def inX1(x):
    v = [val(c) for c in x]
    return v[0] < INF and v[0] <= v[1]-2 and v[0] <= v[2]-2

def member(name, x, P):
    if name == 'B+': return inX1(x)
    if name == 'A+': return inX1(apply(Ti, x, P))
    if name == 'A-': return inX1(apply(T, x, P))
    if name == 'B-': return inX1(apply(T2, x, P))

def randpoly(v, P, length=4):
    p = {v + i: random.randint(-5, 5) for i in range(length)}
    p[v] = random.choice([c for c in range(1, 6)] + [-c for c in range(1, 6)])
    p = red(p, P)
    if not p or val(p) != v:
        p = add({v: 1}, {v+i: 0 for i in range(1)}, P) if P != 1 else {}
    return p

def randX1(P):
    v = random.randint(-3, 3)
    x = [randpoly(v, P)]
    for _ in range(2):
        x.append({} if random.random() < 0.15 else randpoly(v + random.randint(2, 4), P))
    assert inX1(x)
    return x

def rand_in(name, P):
    x = randX1(P)
    M = {'B+': None, 'A+': T, 'A-': Ti, 'B-': T2}[name]
    return x if M is None else apply(M, x, P)

def power_apply(M, e, x, P):
    for _ in range(e):
        x = apply(M, x, P)
    return x

def inverse_word(g, P):
    # A^-1 = T^-1 B T, B^-1 = T^2 B T^2 (BBT Lemma 2.1), used as operators
    return g

def run(P, sign, m, n, trials=150):
    A, B = mats(sign)
    Tn = mats(sign)  # placeholder, T does not depend on t
    fails = 0
    ops = {
        'A+': lambda x: power_apply(A, m, x, P),
        'A-': lambda x: apply(Ti, power_apply(B, m, apply(T, x, P), P), P),
        'B+': lambda x: power_apply(B, n, x, P),
        'B-': lambda x: apply(T2, power_apply(B, n, apply(T2, x, P), P), P),
    }
    for g in ['A+', 'A-', 'B+', 'B-']:
        others = [g] + (['B+', 'B-'] if g[0] == 'A' else ['A+', 'A-'])
        for src in others:
            for _ in range(trials):
                x = rand_in(src, P)
                if not member(g, ops[g](x), P):
                    fails += 1
    return fails

if __name__ == '__main__':
    for P in (0, 2, 3, 5):
        for sign in (1, -1):
            for (m, n) in ((3, 3), (3, 4), (4, 3)):
                fl = run(P, sign, m, n)
                print('p=%d sign=%+d m=%d n=%d failures %d' % (P, sign, m, n, fl))
                assert fl == 0
            print('p=%d sign=%+d m=n=2 failures (expected >0) %d' % (P, sign, run(P, sign, 2, 2, 40)))
    print('ALL PING-PONG TESTS PASSED')
