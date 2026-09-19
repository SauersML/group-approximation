from tchain2 import *
import time
st = {s['trial']: s for s in json.load(open('stalls.json'))}
for tr, dns in ((64, [(1,1)]), (46, [(2,1),(1,2)]), (138, [(2,1),(1,2)]), (122, [(1,1),(2,1),(1,2)])):
    s = st[tr]; bb, cc = s['bs'], s['cs']
    for cm in components(bb, cc):
        B, C = restrict(bb, cc, cm)
        if excess(B, C) == 0: continue
        for dn in dns:
            t0 = time.time(); k, h = least_chain(*pad(B, C, *dn), 4)
            print("trial", tr, "donor", dn, "k", k, h, "%.0fs" % (time.time()-t0), flush=True)
