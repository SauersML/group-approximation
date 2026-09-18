import sys, pickle
from engine_r import *
from crit import pstar
fn, m, K = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
TE, ncl, FM = pickle.load(open(fn,'rb'))
ps = F(pstar(m)).limit_denominator(10**9)
T = matrix(TE, ncl, m, ps); w = wblock(FM, m, ps); L = 3*w*w
Tn = [[float(a/L) for a in r] for r in T]
lam, y = rho_phi(Tn, K, 300)
print('rho', lam)
for r in Tn: print('  ', [round(a,4) for a in r])
