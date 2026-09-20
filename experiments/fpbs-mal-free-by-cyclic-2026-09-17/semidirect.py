"""Check M = <a,b,t | [t,a], t b t^-1 = b a b^-2> is F_3 x|_Theta Z.

F_3 = F(u, v, w) (u = y_-1, v = y_0, w = y_1 with y_i = b^i s b^-i, s = t b^-1),
Theta = conjugation by b:  u -> v,  v -> w,  w -> v u^-1 v^2 w^-1.
Elements of F_3 x| <b> are pairs (word, n) = word * b^n, b x b^-1 = Theta(x).
Checks:
  1. Theta has the inverse u -> u^2 v^-1 w^-1 u, v -> u, w -> v.
  2. t := v b and a := u v^-1 b^2 satisfy [t, a] = 1 and t b t^-1 = b a b^-2.
  3. eps(u)=eps(v)=eps(w)=1 is Theta-invariant, so K = ker eps is normalised
     by b and Gamma_mal = K x| <b>; H_0 = <a, b> = <u v^-1, b>.
  4. Conversely b, t generate: s = t b^-1 = v, and u, w are b-conjugates of v.
"""


def inv(w):
    return [(g, -e) for g, e in reversed(w)]


def red(w):
    st = []
    for x in w:
        if st and st[-1][0] == x[0] and st[-1][1] == -x[1]:
            st.pop()
        else:
            st.append(x)
    return st


def W(s):
    """'uV' style: lower = generator, upper = inverse."""
    return [(c.lower(), 1 if c.islower() else -1) for c in s]


THETA = {'u': W('v'), 'v': W('w'), 'w': W('vUvvW')}
THETA_INV = {'u': W('uuVWu'), 'v': W('u'), 'w': W('v')}


def apply(phi, w, times=1):
    if times < 0:
        return apply(THETA_INV if phi is THETA else THETA, w, -times)
    for _ in range(times):
        out = []
        for g, e in w:
            out += phi[g] if e == 1 else inv(phi[g])
        w = red(out)
    return w


def mul(x, y):
    (w1, n1), (w2, n2) = x, y
    return (red(w1 + apply(THETA, w2, n1)), n1 + n2)


def ginv(x):
    w, n = x
    return (apply(THETA, inv(w), -n), -n)


B = ([], 1)
T = (W('v'), 1)
A = (W('uV'), 2)
ONE = ([], 0)


def comm(x, y):
    return mul(mul(x, y), mul(ginv(x), ginv(y)))


if __name__ == '__main__':
    for g in 'uvw':
        assert apply(THETA_INV, apply(THETA, [(g, 1)])) == [(g, 1)]
        assert apply(THETA, apply(THETA_INV, [(g, 1)])) == [(g, 1)]
    print('1. Theta is an automorphism of F(u,v,w)')
    assert comm(T, A) == ONE
    lhs = mul(mul(T, B), ginv(T))
    rhs = mul(mul(B, A), ginv(mul(B, B)))
    assert lhs == rhs, (lhs, rhs)
    print('2. [t,a] = 1 and t b t^-1 = b a b^-2 hold for t = v b, a = u v^-1 b^2')
    eps = lambda w: sum(e for _, e in w)
    for g in 'uvw':
        assert eps(THETA[g]) == 1
    print('3. eps is Theta-invariant; psi_0(b) = 0, psi_0(t) = eps(v) = 1')
    print('4. s = t b^-1 =', mul(T, ginv(B)))
    # stage generator b-conjugates:  g_i = Theta^i(u v^-1)
    g = W('uV')
    for i in range(0, 4):
        print('   Theta^%d(u v^-1) =' % i,
              ''.join(c if e == 1 else c.upper() for c, e in apply(THETA, g, i)))
