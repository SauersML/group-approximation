# Cross-check between the two censuses: the parity kernel of a (3,3) BMW datum SQ is pi_1 of the 4-vertex complex
# {(h, v, h', v') : SQ(h,v) = (v',h')} (horizontal labels read from column 0, vertical labels from row 0).
# Map every (3,3) BMW class to its 4-vertex class and compare reducibility and SAT outcomes.
import json
from cx4 import canon_orbit
C = json.load(open('census_cx4_33.json')); reps = [tuple(sorted(map(tuple, r))) for r in C['reps']]
out4 = {json.loads(l)['idx']: json.loads(l) for l in open('out_cx4_33.jsonl')}
for pat in ('30_30', '31_30', '31_31'):
    D = json.load(open(f'census_{pat}.json'))
    outb = {json.loads(l)['idx']: json.loads(l) for l in open(f'out_{pat}.jsonl')}
    for i, rep in enumerate(D['reps']):
        S4 = frozenset((h, v, h2, v2) for (h, v), (v2, h2) in rep)
        orb = canon_orbit(S4); hit = [k for k, r in enumerate(reps) if r in orb]; assert len(hit) == 1
        b, q = outb[i], out4[hit[0]]
        irrb = b['finH'] is None or b['finV'] is None; irr4 = q['finH'] is None or q['finV'] is None
        assert irrb == irr4, (pat, i, b, q)
        print(pat, i, '-> cx4 class', hit[0], 'candidate' if irrb else 'reducible')
print('consistent')
