"""Exact checks for the standard-form right-copy no-freezing obstruction.

Replays the calculations of
`standard-form-right-copy-does-not-freeze-zpc-controls` on the standard
form of `M_2(C)` and on its magic-square realization:

  (SFR1) the one-vector correlation survives the side switch;
  (SFR2) the mixed player algebras fail to commute already for `A=W*(Z)`
         inside `B=M_2(C)`;
  (SFR4) the mixed vector state `phi(L(x)R(y))=tau(xy)` is not tracial;
  (SFR6) a relation holding on the selected vector fails on its right ideal;
  (MSS)  the selector realization has `[a,e]=-I`, so a frozen branch would
         force `J=1`.

Arithmetic is exact over the Gaussian rationals; no external packages.
It verifies finite operator identities, not a group-level statement.
"""

from fractions import Fraction as F


class C:
    """A complex number with rational real and imaginary parts."""

    __slots__ = ("re", "im")

    def __init__(self, re=0, im=0):
        self.re, self.im = F(re), F(im)

    def __add__(self, other):
        other = num(other)
        return C(self.re + other.re, self.im + other.im)

    def __sub__(self, other):
        other = num(other)
        return C(self.re - other.re, self.im - other.im)

    def __mul__(self, other):
        other = num(other)
        return C(self.re * other.re - self.im * other.im,
                 self.re * other.im + self.im * other.re)

    __radd__, __rmul__ = __add__, __mul__

    def conj(self):
        return C(self.re, -self.im)

    def __eq__(self, other):
        other = num(other)
        return (self.re, self.im) == (other.re, other.im)

    def __hash__(self):
        return hash((self.re, self.im))

    def __repr__(self):
        if self.im == 0:
            return str(self.re)
        return '%s%s%si' % (self.re, '+' if self.im > 0 else '-', abs(self.im))


def num(x):
    return x if isinstance(x, C) else C(x)


ZERO, ONE, IMAG = C(0), C(1), C(0, 1)


def mat(rows):
    return [[num(x) for x in row] for row in rows]


def eye(n):
    return mat([[1 if i == j else 0 for j in range(n)] for i in range(n)])


def mul(a, b):
    inner = len(b)
    return [[sum((a[i][t] * b[t][j] for t in range(inner)), ZERO)
             for j in range(len(b[0]))] for i in range(len(a))]


def add(a, b):
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))]
            for i in range(len(a))]


def sub(a, b):
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))]
            for i in range(len(a))]


def scale(z, a):
    z = num(z)
    return [[z * a[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def transpose(a):
    return [[a[j][i] for j in range(len(a))] for i in range(len(a[0]))]


def kron(a, b):
    p, q = len(b), len(b[0])
    return [[a[i // p][j // q] * b[i % p][j % q]
             for j in range(len(a[0]) * q)] for i in range(len(a) * p)]


def is_zero(a):
    return all(x == ZERO for row in a for x in row)


def commutator(a, b):
    return sub(mul(a, b), mul(b, a))


def group_commutator(a, b):
    """a b a^-1 b^-1 for self-inverse unitaries."""
    return mul(mul(a, b), mul(a, b))


def trace(a):
    return sum((a[i][i] for i in range(len(a))), ZERO)


def tau(a):
    t, n = trace(a), len(a)
    return C(t.re / n, t.im / n)


# ---------------------------------------------------------------------------
# Standard form of M_2(C): vec(x) is row-major, so L(a)=a (x) I and
# R(b)=I (x) b^T act on C^4 with L(a)vec(x)=vec(ax), R(b)vec(x)=vec(xb).
# ---------------------------------------------------------------------------

X = mat([[0, 1], [1, 0]])
Y = [[ZERO, C(0, -1)], [C(0, 1), ZERO]]
Z = mat([[1, 0], [0, -1]])
P = mat([[1, 0], [0, 0]])                       # p=(1+Z)/2=e_11
E21 = mat([[0, 0], [1, 0]])
OMEGA = [ONE, ZERO, ZERO, ONE]                  # vec(1)


def left(a):
    return kron(a, eye(2))


def right(b):
    return kron(eye(2), transpose(b))


def apply(op, vec):
    return [sum((op[i][j] * vec[j] for j in range(len(vec))), ZERO)
            for i in range(len(op))]


def phi(op):
    """The canonical vector state <op Omega, Omega> on the mixed algebra."""
    image = apply(op, OMEGA)
    total = sum((OMEGA[k].conj() * image[k] for k in range(4)), ZERO)
    return C(total.re / 2, total.im / 2)


def check_actions():
    """The left and right actions commute and (SFR1) holds."""
    for a in (X, Y, Z, P):
        for b in (X, Y, Z, P):
            assert is_zero(commutator(left(a), right(b)))
    for x in (X, Y, Z, P):
        assert phi(mul(left(x), right(P))) == tau(mul(x, P))
    # The correlation is genuinely correlated: an independent tensor copy
    # would report the product of marginals instead.
    assert tau(mul(Z, P)) == C(F(1, 2)) and tau(Z) * tau(P) == ZERO


def check_mixed_algebras_do_not_commute():
    """(SFR2): the cross-commutators of M_A and M_B are the ones in M."""
    assert commutator(X, Z) == scale(C(0, -2), Y)
    assert not is_zero(commutator(left(X), left(Z)))       # L(b) vs L(a)
    assert not is_zero(commutator(right(Z), right(X)))     # R(a) vs R(b)
    # Using R(A) for both players does not help.
    assert not is_zero(commutator(right(P), right(X)))
    assert is_zero(commutator(left(X), left(X)))


def check_state_is_not_tracial():
    """(SFR4): phi(ST) = i and phi(TS) = -i."""
    assert mul(X, Y) == scale(IMAG, Z)
    assert mul(Y, X) == scale(C(0, -1), Z)
    s = left(X)
    t = mul(left(Y), right(Z))
    assert phi(mul(s, t)) == IMAG
    assert phi(mul(t, s)) == C(0, -1)
    assert phi(mul(s, t)) != phi(mul(t, s))


def check_relation_fails_on_the_hull():
    """(SFR5)-(SFR6): (Z-1)p=0, yet L(Z) is -1 on R(p)L^2(M)."""
    assert is_zero(mul(sub(Z, eye(2)), P))
    xi = [E21[i // 2][i % 2] for i in range(4)]             # vec(e_21)
    assert apply(right(P), xi) == xi
    assert apply(left(Z), xi) == [ZERO - v for v in xi]
    assert apply(left(Z), xi) != xi


def check_magic_square_selector():
    """Section 4: [a,e] = -I, so freezing e to a scalar forces J=1."""
    e = kron(Z, eye(2))
    a = kron(X, eye(2))
    minus = scale(-1, eye(4))
    assert mul(e, e) == eye(4) and mul(a, a) == eye(4)
    assert group_commutator(a, e) == minus                  # J = -I
    for sign in (1, -1):
        frozen = scale(sign, eye(4))                        # e becomes J^r
        assert group_commutator(a, frozen) == eye(4)        # forces J = 1
    assert eye(4) != minus


def main():
    check_actions()
    check_mixed_algebras_do_not_commute()
    check_state_is_not_tracial()
    check_relation_fails_on_the_hull()
    check_magic_square_selector()
    s, t = left(X), mul(left(Y), right(Z))
    print('phi(ST), phi(TS) =', phi(mul(s, t)), phi(mul(t, s)))
    print('tau(Zp), tau(Z)tau(p) =', tau(mul(Z, P)), tau(Z) * tau(P))
    print('[a,e] on the selector =', trace(group_commutator(
        kron(X, eye(2)), kron(Z, eye(2)))))
    print('All exact arithmetic checks passed.')


if __name__ == '__main__':
    main()
