import json, subprocess, sys
from swap import excess
from stalls_lib import components, restrict
from tchain import pad
L1, L2 = sys.argv[1], sys.argv[2]
st = json.load(open('stalls.json'))
for s in st:
    bb, cc = s['bs'], s['cs']
    for cm in components(bb, cc):
        B, C = restrict(bb, cc, cm)
        if excess(B, C) == 0: continue
        for dn in [None, (1,1), (2,1), (1,2), (2,2)]:
            b, c = (B, C) if dn is None else pad(B, C, *dn)
            inp = f"{len(b)}\n" + " ".join(map(str,b)) + "\n" + " ".join(map(str,c)) + "\n"
            r = subprocess.run(['./chain2', L1, L2], input=inp, capture_output=True, text=True, timeout=1200)
            print(s['trial'], len(B), dn, r.stdout.strip().replace('\n',' | '), flush=True)
