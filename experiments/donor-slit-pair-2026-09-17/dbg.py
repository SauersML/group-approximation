from tchain2 import *
from collections import Counter
st = {s['trial']: s for s in json.load(open('stalls.json'))}
s = st[64]; bb, cc = s['bs'], s['cs']
for cm in components(bb, cc):
    B, C = restrict(bb, cc, cm)
    if excess(B, C) == 0: continue
    b, c = pad(B, C, 1, 1); ex0 = excess(b, c)
    lab = vertices(b, c)[0]
    cnt = Counter(excess(*apply(b, c, mv)) - ex0 for mv in cand_moves(b, c, lab))
    print(cnt)
    cnt = Counter(excess(*apply(b, c, mv)) - ex0 for mv in all_moves(len(b)) ) if False else None
