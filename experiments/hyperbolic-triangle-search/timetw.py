# timetw.py (sage -python timetw.py): time one twisted integral system of linZ.py (candidate 1, twist
# (0,0,1)) over QQ[z] and over ZZ[z], to estimate the running time of `linZ.py twist`.
from sage.all import *
import sys, time
ns = {"__name__": "linZ"}; exec(open("linZ.py").read(), ns)
cs = {}; exec(open("cands.py").read(), cs)
R2 = PolynomialRing(ZZ, ['c%d' % i for i in range(7)] + ['d%d' % i for i in range(7)] + ['z'], order='degrevlex')
for tw in [(0, 0, 1), (1, 2, 3)]:
    t0 = time.time()
    eqs = ns["system_tw"](cs["CANDS"][0], R2, tw)
    print("twist", tw, "system built: %d equations (%.1fs)" % (len(eqs), time.time() - t0)); sys.stdout.flush()
    RQ = R2.change_ring(QQ)
    gq = RQ.ideal([RQ(f) for f in eqs]).groebner_basis()
    print("twist", tw, "rational GB:", "[1]" if list(gq) == [1] else "len %d" % len(gq), "(%.1fs)" % (time.time() - t0)); sys.stdout.flush()
    gz = R2.ideal(eqs).groebner_basis()
    ints = [f for f in gz if f.is_constant()]
    print("twist", tw, "integral GB integer:", factor(ZZ(ints[0])) if ints else None, "(%.1fs)" % (time.time() - t0)); sys.stdout.flush()
print("TIMETW_DONE")
