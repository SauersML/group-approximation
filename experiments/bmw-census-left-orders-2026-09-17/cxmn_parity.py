# Map every BMW class of degree (4,3) (all involution patterns) to the four-vertex (3,4) class of its parity kernel
# and check that reducibility agrees.  The parity-kernel complex of SQ is {(h, v, h', v') : SQ(h,v) = (v',h')}
# (degree (4,3)); it is transposed to (v', h', v, h) to match census_cx_34.json (3 horizontal, 4 vertical labels).
import json, collections
from cxmn import orbit, normalized
m, n = 3, 4
C = json.load(open('census_cx_34.json')); out4 = {json.loads(l)['idx']: json.loads(l) for l in open('out_cx_34.jsonl')}
def normalize(S):
    d = {(h0, v0): (v1, h1) for h0, v1, h1, v0 in S}
    b = {d[(0, v0)][0]: v0 for v0 in range(n)}; c = {d[(h0, 0)][1]: h0 for h0 in range(m)}
    T = tuple(sorted((h0, b[v1], c[h1], v0) for h0, v1, h1, v0 in S)); assert normalized(T, m, n)
    return T
lookup = {}
for k, r in enumerate(C['reps']):
    for x in orbit(tuple(map(tuple, r)), m, n):
        if normalized(x, m, n): lookup[x] = k
hits = collections.Counter()
for pat in ('40_30', '41_30', '41_31', '42_30', '42_31'):
    D = json.load(open(f'census_{pat}.json')); outb = {json.loads(l)['idx']: json.loads(l) for l in open(f'out_{pat}.jsonl')}
    for i, rep in enumerate(D['reps']):
        S = tuple((v2, h2, v, h) for (h, v), (v2, h2) in rep)
        k = lookup[normalize(S)]; hits[k] += 1
        b, q = outb[i], out4[k]
        assert (b['finH'] is None or b['finV'] is None) == (q['finH'] is None or q['finV'] is None), (pat, i, k)
print('BMW (4,3) classes mapped:', sum(hits.values()), 'into', len(hits), 'of', len(C['reps']), 'cx_34 classes; reducibility consistent')
print('cx_34 classes that are not parity kernels of a (4,3) BMW group:', sorted(set(range(len(C['reps']))) - set(hits)))
