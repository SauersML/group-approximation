from swap import *
import json
from stalls_lib import *
st = json.load(open('stalls.json'))
for s in st:
    b, c = s['bs'], s['cs']
    for cm in components(b, c):
        B, C = restrict(b, c, cm)
        e = excess(B, C)
        if e == 0: continue
        S = Surf(B, C)
        ang = [len(S.cls[v])//4 for v in S.cones()]
        print("trial", s['trial'], "tori", s['sizes'], "comp size", len(cm), "excess", e, "cone angles/2pi", ang)
        print("   horiz cyl (circ,height):", cylinders(B, C), " vert cyl:", cylinders(C, B))
        # distance of stuck state to original torus pair
        print("   rank(bs-b0), rank(cs-c0) =", rank_minus_I(comp(inv(s['b0']), b)), rank_minus_I(comp(inv(s['c0']), c)),
              " start:", rank_minus_I(comp(inv(s['b0']), s['b'])), rank_minus_I(comp(inv(s['c0']), s['c'])))
