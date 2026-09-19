from tchain2 import *
import time
def padm(b, c, sizes):
    for w, h in sizes: b, c = pad(b, c, w, h)
    return b, c
st = json.load(open('stalls.json'))
DON = [[], [(1,1)], [(2,1)], [(1,2)], [(1,1),(1,1)]]
kmax = int(sys.argv[1])
for s in st:
    bb, cc = s['bs'], s['cs']
    for cm in components(bb, cc):
        B, C = restrict(bb, cc, cm)
        if excess(B, C) == 0: continue
        res = []; t0 = time.time()
        for dn in DON:
            k, h = least_chain(*padm(B, C, dn), kmax)
            res.append((dn, k))
            if k is not None and not isinstance(k, tuple) and k <= 2: break
        print("trial", s['trial'], "comp", len(cm), res, "%.0fs" % (time.time()-t0), flush=True)
