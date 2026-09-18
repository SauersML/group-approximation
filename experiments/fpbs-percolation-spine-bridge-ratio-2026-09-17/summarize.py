"""Summarize a directory of brratio outputs into a table.
usage: python3 summarize.py <rundir>
columns: n, h, ratio=Br/TJT (+-jackknife), D=TJT/(n T(u,v)), gam=r*Br/(n T(u,v)) (tilted interior-gap
fraction), ratio*r*D/gam (=1 identically for paths: consistency), K2=T(0,n)/(T(0,n/2)T(n/2,n)),
q=P(volume meets infinity off Lambda), theta=P(mid vertex in spine),
Dg=lam+1/lam with lam=T(0,n)/T(0,n-1): the value of D for an exactly geometric t (no coverage correlation)"""
import sys, os, re, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ana import main
rows = {}
for f in sorted(glob.glob(os.path.join(sys.argv[1], '*.out'))):
    b = os.path.basename(f)[:-4]
    m = re.match(r'(.*)_n(\d+)(?:_h(\d+))?$', b)
    if not m: continue
    try: hdr, full, err, W = main([f])
    except Exception: continue
    rows.setdefault(m.group(1), []).append((int(m.group(2)), int(m.group(3) or 0), hdr, full, err, W))
for key in sorted(rows):
    hdr = rows[key][0][2]
    print('== %s  (type=%s pp=%s r=%s M=%s)' % (key, hdr['type'], hdr['pp'], hdr['r'], hdr['M']))
    print('   %5s %3s %10s %8s %8s %8s %8s %7s %7s %7s' % ('n', 'h', 'ratio', '+-', 'D', 'gam', 'K2', 'q', 'theta', 'Dg'))
    r = float(hdr['r'])
    for n, h, _, fu, er, W in sorted(rows[key], key=lambda z: (z[1], z[0])):
        D = fu['TJTT'] / n; gam = r * fu['BrT'] / n
        print('   %5d %3d %10.4g %8.2g %8.4g %8.4g %8.4g %7.3f %7.3f %7.3f' % (n, h, fu['ratio'], er['ratio'], D, gam, fu['K2'], fu['q'], fu['theta'], fu['lam']+1/fu['lam']))
