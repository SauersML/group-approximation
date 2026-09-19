# Back-translate the J-certificate to d_x in ZG and verify sum_x c_x d_x = 1 in ZG directly.
from zg import rmul, radd
from redJ import C
from redJ import T, TAU, fphi, fmul, fadd
from solveQ import solve
Y = {('', 1): 1}; YI = {('', -1): 1}
def zf(h): return {(u, 0): v for u, v in h.items()}
def z_add(E, F, s=1):
    out = dict(E)
    for k, v in F.items(): out[k] = radd(out.get(k, {}), v, s)
    return {k: v for k, v in out.items() if v}
def z_rmul(E, a): return {k: rmul(v, a) for k, v in E.items()}
# tracked element: (val in ZF, E) standing for the ZG element val + sum_z c_z E_z
def tr_y(t):
    val, E = t
    E2 = z_rmul(E, Y)
    E2 = z_add(E2, {'a': zf(fmul({'p': -1}, fphi(val, -1)))})
    return (T(val), E2)
def tr_yi(t):
    val, E = t
    ph = fphi(val, 1)
    E2 = z_rmul(E, YI)
    E2 = z_add(E2, {'a': zf(fmul({'pQs': -1}, ph)), 'e': zf(fmul({'r': 1}, ph))})
    return (fmul(fmul(TAU, {'Qs': 1}), ph), E2)
def tr_f(t, f):
    val, E = t
    return (fmul(val, f), z_rmul(E, zf(f)))
def tr_add(t, t2, s=1):
    return (fadd(t[0], t2[0], s), z_add(t[1], t2[1], s))
ONE = ({'': 1}, {})
def rightform(el):
    from zg import phipow
    out = {}
    for (u, m), v in el.items():
        d = out.setdefault(m, {}); w = phipow(u, -m); d[w] = d.get(w, 0) + v
    return out
def tracked(el):
    tot = ({}, {})
    for m, f in rightform(el).items():
        t = ONE
        for _ in range(abs(m)): t = tr_y(t) if m > 0 else tr_yi(t)
        tot = tr_add(tot, tr_f(t, f))
    return tot
# generators of J with their expressions  gen = sum_z c_z coef_z
def gen_exprs():
    out = {}
    for x in 'bcd':
        val, E = tracked(C[x])
        out['red_' + x] = (val, z_add({x: {('', 0): 1}}, E, -1))
    val, E = tr_y(tr_yi(ONE))           # 1 = val + sum c_z E_z
    out['je'] = (fadd(val, {'': 1}, -1), {k: {kk: -vv for kk, vv in v.items()} for k, v in E.items()})
    return out
def tstep(gen):
    val, coef = gen                      # val = sum c_z coef_z (in ZG)
    new = z_rmul(coef, Y)
    new = z_add(new, {'a': zf(fmul({'p': 1}, fphi(val, -1)))})
    return (T(val), new)
def check_expr(gen):
    val, coef = gen
    tot = {}
    for z, e in coef.items(): tot = radd(tot, rmul(C[z], e))
    return tot == zf(val)
if __name__ == '__main__':
    GE = gen_exprs()
    GE1 = {(n, 0): g for n, g in GE.items()}
    GE1.update({(n, 1): tstep(g) for n, g in GE.items()})
    for k, g in GE1.items(): print(k, 'expression ok', check_expr(g))
    _, sol, ok = solve(3)
    D = {}
    for ((name, k), w), v in sol:
        val, coef = GE1[(name, k)]
        for z, e in coef.items(): D[z] = radd(D.get(z, {}), rmul(e, {(w, 0): int(v)}))
    tot = {}
    for z, e in D.items(): tot = radd(tot, rmul(C[z], e))
    print('sum_x c_x d_x =', tot)
    print('CERTIFICATE', tot == {('', 0): 1})
    for z in 'abcde': print('d_' + z, len(D.get(z, {})), 'terms')

