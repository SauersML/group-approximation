"""Check the twisted Lemma 5.6 bound (here k = F_p, e = 1, d = dim M).

t   = cls/d = number of independent Q-equivariant classes A' -> M produced by the
      lifted cocycles (cls counts their F_p-coordinates; each nonzero equivariant
      map onto the irreducible M contributes d independent coordinates).
Lemma:  t >= x0*v0 - r*d,  i.e. in crown units  t/d >= x0*v0/d - r.

x0 = dim C(K cap ker Xi): rank of the scalar classes U on A' = K cap ker Xi.
v0 = dim_k V0 where Xi(K cap ker C) = M (x) V0, i.e. dim Xi(K cap ker C)/dim M.
Both computed from Schreier generators of the relevant finite-index subgroup,
using covers of the presentation 2-complex (relators do not affect 1-skeleton
loops generating the subgroup of the free group; images are homomorphisms that
vanish on relators, so free-group Schreier generators suffice).
"""
import numpy as np
from twisted_lift import Setup, rank_mod_p

def schreier_images(S, U, C, key_fn):
    p, d = S.p, S.d
    h = len(C)
    xis = [[C[j][d*s:d*(s+1)] for s in range(S.ngen)] for j in range(h)]
    # full state: (rho matrix, xi vector (h*d), C vector (u))
    def step(st, s):
        Qm, X, Cv = st
        nQ = Qm @ S.rho[s] % p
        nX = (X + np.array([Qm @ xis[j][s] for j in range(h)]).reshape(h, d)) % p
        nC = (Cv + np.array([U[i][s] for i in range(len(U))])) % p
        return (nQ, nX, nC)
    st0 = (np.eye(d, dtype=np.int64), np.zeros((h, d), dtype=np.int64), np.zeros(len(U), dtype=np.int64))
    index = {key_fn(st0): 0}; states = [st0]
    loopsC, loopsX = [], []
    i = 0
    while i < len(states):
        for s in range(S.ngen):
            ns = step(states[i], s)
            k = key_fn(ns)
            if k not in index:
                index[k] = len(states); states.append(ns)
            else:
                old = states[index[k]]
                loopsC.append((ns[2] - old[2]) % p)
                loopsX.append(((ns[1] - old[1]) % p).flatten())
        i += 1
        if len(states) > 300000:
            raise RuntimeError("too big")
    return loopsC, loopsX

def bound(S, U, C):
    p, d = S.p, S.d
    # A' = K cap ker Xi : key = (rho, xi)
    kA = lambda st: (tuple(st[0].flatten()), tuple(st[1].flatten()))
    LC, _ = schreier_images(S, U, C, kA)
    x0 = rank_mod_p(np.array(LC), p) if LC else 0
    # K cap ker C : key = (rho, C)
    kK = lambda st: (tuple(st[0].flatten()), tuple(st[2].flatten()))
    _, LX = schreier_images(S, U, C, kK)
    dimY0 = rank_mod_p(np.array(LX), p) if LX else 0
    return x0, dimY0 / d

if __name__ == "__main__":
    T=[[0,1],[1,0]]; O=[[0,1],[1,1]]; I2=[[1,0],[0,1]]
    from twisted_lift import run_case
    def comm(x,y): return [(x,1),(y,1),(x,-1),(y,-1)]
    cases = [
        ("F2 S3 both U", 2, 2, [], [T,O], None, None, None),
        ("F2 S3 U=x (sign)", 2, 2, [], [T,O], [0], None, None),
        ("F2 S3 U=y", 2, 2, [], [T,O], [1], None, None),
        ("F3 S3", 2, 3, [], [T,O,I2], None, None, None),
        ("S2 h=2 all U", 2, 4, [comm(0,1)+comm(2,3)], [T,I2,O,I2], None, [0,1], None),
        ("S2 h=2 U=sign(a)", 2, 4, [comm(0,1)+comm(2,3)], [T,I2,O,I2], None, [0,1], [[1,0,0,0]]),
        ("S2 h=3 all U", 2, 4, [comm(0,1)+comm(2,3)], [T,I2,O,I2], None, [0,1,2], None),
    ]
    for name, p, n, R, rho, Usel, Csel, Uex in cases:
        S = Setup(p, n, R, rho)
        U = S.scalar_cocycles()
        if Usel is not None: U = np.array([U[i] for i in Usel])
        if Uex is not None: U = np.array(Uex, dtype=np.int64)
        C = S.derivations_mod_coboundaries()
        if Csel is not None: C = np.array([C[j] for j in Csel])
        res = S.run(U, C)
        x0, v0 = bound(S, U, C)
        d = S.d
        t = res['cls'] / d
        b = x0 * v0 - res['r'] * d
        print(name, dict(z=res['z'], cls=res['cls'], t=t, x0=x0, v0=v0, r=res['r'], d=d,
                         bound_t=b, ok=(res['cls'] % d == 0 and t >= b), tight=(t == b)), flush=True)
