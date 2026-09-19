# Screen slide-group variants Gamma'' = <x,y,t | f(u0), f(u1)> for homomorphisms to small
# perfect groups with t != 1 (vectorised over (y,t); x runs over conjugacy-class reps).
# Every variant maps onto G = <x,y|w> under t -> 1 and has the same relation-module class
# (Qkappa unitriangular), so a hom with t != 1 is a pure relation-gap witness.
import sys, os, json, random, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'c2-free-by-cyclic-2026-09-18'))
from verify_unimodular import D, BAS, U0, U1, inv, fred, W
import groups
CACHE = os.environ.get('SCREEN_CACHE', '/tmp')

def load(name):
    f = os.path.join(CACHE, 'grp_%s.npz' % name)
    if os.path.exists(f):
        z = np.load(f); return z['mul'], z['inv'], int(z['e']), list(z['reps'])
    n, mul, iv, e, reps = groups.get(name)
    mul = np.array(mul, dtype=np.int32); iv = np.array(iv, dtype=np.int32)
    try: np.savez(f, mul=mul, inv=iv, e=e, reps=np.array(reps))
    except OSError: pass
    return mul, iv, e, reps

def cyc(u):
    while len(u) > 1 and u[0] == u[-1].swapcase(): u = u[1:-1]
    return u

def build(Dv, extra=None, sgn=1):
    """Dv[z] = list of (n, u): Pi_z = prod u t^(sgn n) u^-1.  extra[z] = word in x,y,t
    trivial in G under t -> 1 appended to f(z).  Returns (R0, R1)."""
    tt = 't' if sgn > 0 else 'T'
    def Pi(z): return ''.join(u + (tt if n > 0 else tt.swapcase()) * abs(n) + inv(u) for n, u in Dv[z])
    SUB = {z: fred(inv(Pi(z)) + BAS[z] + ((extra or {}).get(z, ''))) for z in 'abcde'}
    def subst(u): return fred(''.join(SUB[ch] if ch.islower() else inv(SUB[ch.lower()]) for ch in u))
    return cyc(subst(U0)), cyc(subst(U1))

def homs(R, grp, limit=None):
    """Count homs <x,y,t | R> -> grp with t != 1, x up to conjugacy."""
    mul, iv, e, reps = grp; n = len(iv)
    Y = np.repeat(np.arange(n, dtype=np.int32), n); T = np.tile(np.arange(n, dtype=np.int32), n)
    keep = T != e; Y, T = Y[keep], T[keep]
    tot = 0; wit = None
    for xi in reps:
        im = {'x': xi, 'X': iv[xi], 'y': Y, 'Y': iv[Y], 't': T, 'T': iv[T]}
        yy, ts = Y, T
        for r in R:
            ims = {k: v for k, v in im.items()}
            g = np.full(len(yy), e, dtype=np.int32)
            for c in r: g = mul[g, ims[c]]
            ok = g == e
            yy, ts = yy[ok], ts[ok]
            im = {'x': xi, 'X': iv[xi], 'y': yy, 'Y': iv[yy], 't': ts, 'T': iv[ts]}
            if len(yy) == 0: break
        tot += len(yy)
        if len(yy) and wit is None: wit = (xi, int(yy[0]), int(ts[0]))
    return tot, wit

def mutate(rng, Dv, mode):
    """Random variant preserving the Z[G]-coefficients of Pi_z (hence kappa)."""
    Dn = {z: list(v) for z, v in Dv.items()}
    ws = [W, inv(W), 'x' + W + 'X', 'y' + W + 'Y', 'X' + inv(W) + 'x', 'Y' + W + 'y']
    for z in Dn:
        if 'perm' in mode: rng.shuffle(Dn[z])
        if 'wins' in mode:
            Dn[z] = [(n, u + rng.choice(ws) if rng.random() < 0.5 else u) for n, u in Dn[z]]
        if 'pair' in mode and rng.random() < 0.5:
            u = rng.choice(['', 'x', 'y', 'X', 'Y', 'xy', 'yx', 'XY'])
            k = rng.randrange(len(Dn[z]) + 1)
            Dn[z][k:k] = [(1, u), (-1, u + rng.choice(ws))]
    return Dn

if __name__ == '__main__':
    names = sys.argv[1].split(',') if len(sys.argv) > 1 else ['A5']
    nvar = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    mode = sys.argv[3] if len(sys.argv) > 3 else 'perm'
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    grps = {nm: load(nm) for nm in names}
    rng = random.Random(seed)
    for vi in range(nvar + 1):
        for sgn in (1, -1):
            Dv = D if vi == 0 else mutate(rng, D, mode)
            R = build(Dv, sgn=sgn)
            res = []
            for nm in names:
                c, wit = homs(R, grps[nm]); res.append('%s:%d' % (nm, c))
            print('var', vi, 'sgn', sgn, 'len', len(R[0]), len(R[1]), ' '.join(res), flush=True)
            if all(r.endswith(':0') for r in res) and os.environ.get('SURVIVORS'):
                with open(os.environ['SURVIVORS'], 'a') as fh:
                    fh.write(json.dumps({'mode': mode, 'seed': seed, 'var': vi, 'sgn': sgn,
                                         'D': Dv, 'R0': R[0], 'R1': R[1]}) + '\n')
