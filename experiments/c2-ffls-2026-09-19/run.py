"""Scan transitive rho: H -> S_n up to conjugacy (by the centralizer of the fixed b), compute the
twisted Alexander torsion order and certify every non-bi-monic irreducible factor exactly.
Usage: python3 run.py N [MAXREPS] [TRIALS]"""
import sys, time
import twisted as T

def canon(im, cb):
    best = None
    for g in cb:
        gi = T.inv(g)
        key = tuple(T.mul(T.mul(g, im[x]), gi) for x in 'cde')
        if best is None or key < best: best = key
    return (im['b'],) + best

if __name__ == '__main__':
    n = int(sys.argv[1]); maxreps = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    t0 = time.time(); seen = set(); orders = {}; cnt = 0; certs = []
    cbs = {}
    for im in T.reps(n):
        b = im['b']
        if b not in cbs: cbs[b] = T.centralizer(b)
        k = canon(im, cbs[b])
        if k in seen: continue
        seen.add(k); cnt += 1
        if cnt > maxreps: break
        P = T.polymat(T.fox(im, n), n)
        rk, tor = T.torsion(P, n, trials=trials)
        if tor.is_zero():
            orders.setdefault('ZERO', [0, im])[0] += 1; continue
        _, fs = tor.factor()
        fs = [(f, e) for f, e in fs if f != T.fmpz_poly([0, 1])]
        bad = [f for f, e in fs if not T.bimonic(f)]
        cert = [f for f in bad if T.rank_mod(P, f) < rk]
        good = [(f, e) for f, e in fs if f not in bad or f in cert]
        key = ' '.join(sorted('(%s)^%d' % (f, e) for f, e in good))
        orders.setdefault(key, [0, im])[0] += 1
        if cert:
            certs.append((im, [str(f) for f in cert]))
            print('CERTIFIED NON-BIMONIC', T.fmt(im), [str(f) for f in cert], flush=True)
    for key, (c, im) in sorted(orders.items(), key=lambda kv: -kv[1][0]):
        print('%6d  %s   e.g. %s' % (c, key, T.fmt(im)))
    print('n=%d: %d classes, %d certified non-bimonic, %.0fs' % (n, cnt, len(certs), time.time() - t0))
