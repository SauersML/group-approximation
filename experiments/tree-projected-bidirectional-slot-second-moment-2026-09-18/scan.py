import sys, subprocess, os, time, crit, lump, anal
import engine_r as engine
def deco(kind, m):
    if kind == 'ap': A = list(range(m)); B = list(range(m))
    elif kind == 'nr':   # near-AP rigid
        A = list(range(m - 1)) + [m]; B = list(range(m - 2)) + [m - 1, m]
    elif kind == 'nr2':  # rigid, gaps at both ends
        A = [0] + list(range(2, m + 1)); B = list(range(m - 1)) + [m + 1]
    return A, B
kind, R = sys.argv[1], sys.argv[2]
for m in map(int, sys.argv[3:]):
    A, B = deco(kind, m)
    fn = 'tmp_%s_%s_%d.txt' % (kind, R.replace(',', '_'), m)
    t = time.time()
    with open(fn, 'w') as f:
        subprocess.run(['./pairx', os.environ.get('C','1'), R, str(len(A))] + list(map(str, A)) + [str(len(B))] + list(map(str, B)), stdout=f, check=True)
    hi, ps, up, low = crit.crit(fn, m)
    ctx = anal.load(fn)
    Tl, w2 = lump.lumped_T(ctx, ps, int(os.environ.get('C','1')))
    ll, _ = engine.rho_phi([[a / (3 * w2) for a in r] for r in Tl], 1, 300)
    print('c=' + os.environ.get('C','1') + ' %s R=%s m %2d  m*p_crit %.5f  m*p* %.5f  rho_up %.5f rho_low %.5f lumped %.5f %s  (%.0fs)' % (
        kind, R, m, m * hi, m * ps, up, low, ll, 'PASS' if up < 1 else 'fail', time.time() - t), flush=True)
    os.remove(fn)
