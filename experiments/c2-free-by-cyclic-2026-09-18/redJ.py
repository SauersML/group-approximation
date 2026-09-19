# Reduce N = ZG / sum c_x ZG to ZF / J.
# N is generated over ZF by [1]:  c_a = alpha0 + y alpha1 (alpha1 unit) gives [y h] = [tau h],
# tau = -alpha0 alpha1^-1.  So [1] . y = T(1) with T(h) = tau phi^-1(h), and J = ZF cap I is the
# smallest T-stable right ideal containing red(c_x) for all x.
from fbc import apply, PHI, PHII, red, inv
from zg import rmul, radd, fox, u0, u1, g, mul, ginv, phipow
def fmul(a, b):
    out = {}
    for u, s in a.items():
        for v, t in b.items():
            k = red(u + v); out[k] = out.get(k, 0) + s * t
    return {k: v for k, v in out.items() if v}
def fadd(a, b, s=1):
    out = dict(a)
    for k, v in b.items(): out[k] = out.get(k, 0) + s * v
    return {k: v for k, v in out.items() if v}
def fphi(a, m): return {phipow(u, m): v for u, v in a.items()}
def rightform(el):
    # el = sum coef * (u y^m) ; u y^m = y^m phi^-m(u) ; return {m: ZF element}
    out = {}
    for (u, m), v in el.items():
        d = out.setdefault(m, {}); w = phipow(u, -m); d[w] = d.get(w, 0) + v
    return {m: {k: v for k, v in d.items() if v} for m, d in out.items()}
C = {z: radd(rmul({g: 1}, fox(u0, z)), fox(u1, z), -1) for z in 'abcde'}
RC = {z: rightform(C[z]) for z in C}
assert set(RC['a']) == {0, 1} and len(RC['a'][1]) == 1
(w1, c1), = RC['a'][1].items()
assert abs(c1) == 1
unit_inv = {inv(w1): c1}           # alpha1^-1 (c1 = +-1)
TAU = {k: -v for k, v in fmul(RC['a'][0], unit_inv).items()}
# c_e gives y^2 = u (mod I) with u a unit: read it off from red of y^2 two ways below.
def T(h): return fmul(TAU, fphi(h, -1))
def Tpow(h, k):
    assert k >= 0
    for _ in range(k): h = T(h)
    return h
def redN(el, Tinv):
    out = {}
    for m, f in rightform(el).items():
        base = Tpow({'': 1}, m) if m >= 0 else Tinvpow({'': 1}, -m, Tinv)
        out = fadd(out, fmul(base, f))
    return out
def Tinvpow(h, k, Tinv):
    for _ in range(k): h = Tinv(h)
    return h
if __name__ == '__main__':
    print('tau', TAU)
    for z in 'abcde': print(z, {m: len(f) for m, f in sorted(RC[z].items())}, RC[z])
def Tinv(h): return fmul(fmul(TAU, {'Qs': 1}), fphi(h, 1))
def gens0():
    S = {}
    for z in 'abcde': S['red_' + z] = redN(C[z], Tinv)
    S['je'] = fadd(T(Tinv({'': 1})), {'': 1}, -1)
    S['je2'] = fadd(Tinv(T({'': 1})), {'': 1}, -1)
    return {k: v for k, v in S.items() if v}
def orbit(S, kmin, kmax):
    out = {}
    for name, h in S.items():
        cur = h
        for k in range(0, kmax + 1):
            out[(name, k)] = cur; cur = T(cur)
        cur = h
        for k in range(1, -kmin + 1):
            cur = Tinv(cur); out[(name, -k)] = cur
    return out
def maxlen(h): return max(len(u) for u in h)
