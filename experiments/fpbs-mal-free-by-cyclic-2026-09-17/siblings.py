"""Stage relations of the three exceptional kernels of M = F_3 x|_Theta <b>.

Characters psi = (psi(b), psi(t)).  In M the exceptional rays are
  psi_0 = (0,1)  kernel Gamma_mal, generators b_i = t^i b t^-i,
  psi_1 = (1,0)  kernel N_1,       generators y_i = b^i t b^-i,
  psi_2 = (1,2)  kernel N_2,       generators y_i = b^i (t b^-2) b^-i.
Checked identities (all in the faithful model F(u,v,w) x|_Theta <b>):
  G0  b_2 = b_1 b_0^-1 b_1 b_0^2 b_1^-2                 (Gamma_mal ascends)
  N1  y_-2 g y_-2^-1 = y_-1^-1,  g = y_-1^-1 y_1^-1 y_-1  (commensuration)
      and y_1 in <y_-2, y_-1, y_0> via y_1 = y_-1 y_-2^-1 y_-1 y_-2 y_-1^-1
  N2  y_3^2 = y_1 y_0^-1 y_1 y_2                         (square root)
      and y_-1 = y_0 y_1 y_2^-2 y_0
Also: psi(g) = 0 for the elements used, and the kernels contain K.
"""
from semidirect import mul, ginv, B, T, ONE


def pw(x, n):
    r = ONE
    base = x if n >= 0 else ginv(x)
    for _ in range(abs(n)):
        r = mul(r, base)
    return r


def conj(g, x):
    return mul(mul(g, x), ginv(g))


def prod(*xs):
    r = ONE
    for x in xs:
        r = mul(r, x)
    return r


def I(x):
    return ginv(x)


if __name__ == '__main__':
    bb = {i: conj(pw(T, i), B) for i in range(-3, 4)}
    lhs = bb[2]
    rhs = prod(bb[1], I(bb[0]), bb[1], bb[0], bb[0], I(bb[1]), I(bb[1]))
    assert lhs == rhs
    print('G0 ok: b_2 = b_1 b_0^-1 b_1 b_0^2 b_1^-2')

    y = {i: conj(pw(B, i), T) for i in range(-4, 5)}
    g = prod(I(y[-1]), I(y[1]), y[-1])
    assert conj(y[-2], g) == I(y[-1])
    assert y[1] == prod(y[-1], I(y[-2]), y[-1], y[-2], I(y[-1]))
    assert g != ONE
    print('N1 ok: y_-2 (y_-1^-1 y_1^-1 y_-1) y_-2^-1 = y_-1^-1 ; y_1 in <y_-2,y_-1,y_0>')

    z0 = mul(T, pw(B, -2))
    z = {i: conj(pw(B, i), z0) for i in range(-4, 5)}
    assert mul(z[3], z[3]) == prod(z[1], I(z[0]), z[1], z[2])
    assert z[-1] == prod(z[0], z[1], I(z[2]), I(z[2]), z[0])
    assert mul(z[3], z[3]) != ONE
    print('N2 ok: y_3^2 = y_1 y_0^-1 y_1 y_2 ; y_-1 = y_0 y_1 y_2^-2 y_0')

    # sanity: word lengths of the stage elements grow (no accidental identities)
    for name, el in [('b_2', bb[2]), ('y_1 (N1)', y[1]), ('y_3 (N2)', z[3])]:
        print('  ', name, 'F_3-part length', len(el[0]), 'b-exponent', el[1])
