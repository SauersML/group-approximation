# stat_lin.py (sage -python stat_lin.py <members file> <mode>): power calibration of the linear
# searches on random members of the family F. mode d4c2 uses lin4.analyse; d6c2, d7p29 use
# linD.analyse. Prints one line per member and a tally. A member with a representation is a
# member WITH a finite quotient, so a nonzero rate means the search can see structure in F.
from sage.all import *
import sys, time
ns4 = {"__name__": "lin4"}; exec(open("lin4.py").read(), ns4)
nsD = {"__name__": "linD"}; exec(open("linD.py").read(), nsD)
mf, mode = sys.argv[1], sys.argv[2]
ns = {}; exec(open(mf).read(), ns); MEM = ns["CANDS"]
E = libgap.eval; A7 = libgap.AlternatingGroup(7); A8 = libgap.AlternatingGroup(8)
words = [(i, j) for i in range(1, 7) for j in range(1, 7)]
words += [(i, j, k, l) for i in range(1, 4) for j in range(1, 4) for k in range(1, 4) for l in range(1, 4)]
if mode == "d6c2":
    Rx = PolynomialRing(GF(2), 'x'); xx = Rx.gen()
    K = GF(8, 'w', modulus=xx**3 + xx + 1); om = K.gen(); d, norm = 6, 1
    mods = (nsD["heart2"], nsD["heart2"], nsD["heart2"])
elif mode == "d7p29":
    K = GF(29); om = K.multiplicative_generator()**4; d, norm = 7, 2
    pm = lambda g, F: nsD["permmat"](g, 7, F)
    mods = (pm, pm, nsD["heart0"])
tally = {}; t0 = time.time()
for k, c in enumerate(MEM, 1):
    pr = tuple([E(s) for s in c[X]] for X in "ABC")
    if mode == "d4c2":
        res = ns4["analyse"]("m%d" % k, A7, pr[0], A7, pr[1], A8, pr[2], tuple(c["e"]))
        kinds = sorted(set(r for tag, r in res))
        if all(r.startswith("charpoly") for r in kinds):
            summary = "sigma=-1 (no type triple)"
        elif any("points" in r for r in kinds):
            summary = "REPRESENTATION: " + " | ".join(r for tag, r in res if "points" in r)
        elif any("dimension" in r for r in kinds):
            summary = "positive-dimensional trace ideal"
        else:
            summary = "sigma=+1, trace ideals (1)"
    else:
        summary = nsD["analyse"]("m", mods, pr, (A7, A7, A8), tuple(c["e"]), K, om, d, norm, words)
        if "NOT (1)" in summary: summary = "REPRESENTATION: " + summary
    tally[summary.split(":")[0] if summary.startswith("REPRESENTATION") else summary] = \
        tally.get(summary.split(":")[0] if summary.startswith("REPRESENTATION") else summary, 0) + 1
    print("MEMBER %d %s e=%s :: %s" % (k, mode, c["e"], summary)); sys.stdout.flush()
print("STAT %s members=%d tally=%s %.1fs" % (mode, len(MEM), tally, time.time() - t0))
