# Polynomials over F_p (p odd prime) as tuples of coefficients, lowest degree first, no trailing zeros.
P = 3
def setp(p):
    global P; P = p
def tr(a):
    a = list(a)
    while a and a[-1] % P == 0: a.pop()
    return tuple(x % P for x in a)
def add(a, b):
    n = max(len(a), len(b)); return tr([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)])
def neg(a): return tuple((-x) % P for x in a)
def sub(a, b): return add(a, neg(b))
def mul(a, b):
    if not a or not b: return ()
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b): c[i + j] += x * y
    return tr(c)
def smul(s, a): return tr([s * x for x in a])
def divmod_(a, b):
    a = list(a); q = [0] * max(len(a) - len(b) + 1, 1); ib = pow(b[-1], P - 2, P)
    while len(a) >= len(b) and a:
        c = a[-1] * ib % P; d = len(a) - len(b); q[d] = c
        for i, y in enumerate(b): a[i + d] = (a[i + d] - c * y) % P
        a = list(tr(a))
    return tr(q), tr(a)
def gcd(a, b):
    while b: a, b = b, divmod_(a, b)[1]
    return monic(a) if a else a
def monic(a):
    if not a: return a
    return smul(pow(a[-1], P - 2, P), a)
def val(a, pl):
    if not a: return 10 ** 9
    v = 0
    while True:
        q, r = divmod_(a, pl)
        if r: return v
        a = q; v += 1
def powmod(a, e, m):
    r = (1,); a = divmod_(a, m)[1]
    while e:
        if e & 1: r = divmod_(mul(r, a), m)[1]
        a = divmod_(mul(a, a), m)[1]; e >>= 1
    return r
def legendre(a, pl):
    """quadratic character of a (unit mod pl) in F_p[t]/(pl): 1 or -1"""
    r = powmod(a, (P ** (len(pl) - 1) - 1) // 2, pl)
    assert r in ((1,), (P - 1,)), (a, pl, r)
    return 1 if r == (1,) else -1
def irreducibles(maxdeg):
    import itertools
    out = []
    for d in range(1, maxdeg + 1):
        for c in itertools.product(range(P), repeat=d):
            f = tuple(c) + (1,)
            if all(divmod_(f, g)[1] for g in out if len(g) <= d // 2 + 1 and len(g) < len(f)): out.append(f)
    return out
def factor_places(a, irr):
    return [g for g in irr if len(g) <= len(a) and not divmod_(a, g)[1]]
