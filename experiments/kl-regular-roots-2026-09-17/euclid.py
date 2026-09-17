"""Regular roots in the crystallographic group Z[omega] x| C_6.

Elements (a, k): z -> omega^k z + a, a = a1 + a2*omega in Z[omega], omega = e^(i pi/3).
A word wbar over F = C_6 = <c>, c = (0, 1), and a candidate root tau.
The Fox derivative D = sum eps_j s'_j lies in Z[Gamma'], Gamma' = A x| C_6, A = Z[omega].
Right multiplication by D on Q[Gamma'] = (+)_l Q[A] e_l, e_l = (0, l), is Q[A]-linear:
e_l * (a, k) = x^(omega^l a) e_(l+k).  Its 6x6 determinant over the Laurent ring Q[A]
is non-zero iff D has no left annihilator in Q[Gamma'] (Q[A] is a domain), i.e. iff the
root is regular over Z.
"""
import sympy as sp

def rot(a, k):
    a1, a2 = a
    for _ in range(k % 6):
        a1, a2 = -a2, a1 + a2
    return (a1, a2)

def mul(g, h):
    (a, k), (b, l) = g, h
    rb = rot(b, k)
    return ((a[0] + rb[0], a[1] + rb[1]), (k + l) % 6)

def inv(g):
    a, k = g
    ra = rot(a, -k)
    return ((-ra[0], -ra[1]), (-k) % 6)

E = ((0, 0), 0)

def evalword(word, tau):
    u = E; ti = inv(tau)
    for kind, v in word:
        u = mul(u, v if kind == 'g' else (tau if v == 1 else ti))
    return u

def fox(word, tau):
    D = {}; u = E; ti = inv(tau)
    for kind, v in word:
        if kind == 'g':
            u = mul(u, v)
        elif v == 1:
            D[u] = D.get(u, 0) + 1; u = mul(u, tau)
        else:
            u = mul(u, ti); D[u] = D.get(u, 0) - 1
    return {g: e for g, e in D.items() if e}

X, Y = sp.symbols('x y')

def right_matrix(D):
    M = sp.zeros(6, 6)
    for (a, k), e in D.items():
        for l in range(6):
            b = rot(a, l)
            M[(l + k) % 6, l] += e * X**b[0] * Y**b[1]
    return M

def det_laurent(M):
    return sp.factor(sp.expand(M.det(method='berkowitz')))

C = lambda k: ((0, 0), k % 6)

def parse(s):
    w = []
    for tok in s.split():
        if tok == 't': w.append(('t', 1))
        elif tok == 'T': w.append(('t', -1))
        else: w.append(('g', C(int(tok))))
    return w
