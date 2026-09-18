# Locate the named calibration complexes (Radu's (3,3) complex, Janzen-Wise) in the census and print their records.
import json
from vh_enum import transforms, key, valid, inv_arr
NAMED = {
    'radu': dict(pat='30_30', H='abc', V='xyz', inv={c: c for c in 'abcxyz'},
                 rel=['axax', 'ayay', 'azbz', 'bxbx', 'bycy', 'cxcz']),
    'janzen-wise': dict(pat='42_42', H='aAbB', V='xXyY',
                        inv={'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b', 'x': 'X', 'X': 'x', 'y': 'Y', 'Y': 'y'},
                        rel=['axay', 'aXbY', 'aYBX', 'bxBY']),
}
def build(G):
    H, V, I = G['H'], G['V'], G['inv']; SQ = {}
    def put(h, v, v2, h2):
        assert (h, v) not in SQ or SQ[(h, v)] == (v2, h2); SQ[(h, v)] = (v2, h2)
    for r in G['rel']:
        h1, v1, h2, v2 = r
        put(h1, v1, I[v2], I[h2]); put(h2, v2, I[v1], I[h1])
        put(I[h2], I[v1], v2, h1); put(I[h1], I[v2], v1, h2)
    return {(H.index(h), V.index(v)): (V.index(v2), H.index(h2)) for (h, v), (v2, h2) in SQ.items()}
for name, G in NAMED.items():
    D = json.load(open(f"census_{G['pat']}.json"))
    m, n, iA, iB = D['m'], D['n'], D['iA'], D['iB']
    SQ = build(G); assert valid(SQ, m, n, iA, iB)
    SA, SB, relab, rev, swp = transforms(m, n, iA, iB, True)
    base = [SQ, rev(SQ)] + ([swp(SQ), rev(swp(SQ))] if D['m'] == D['n'] and D['pA'] == D['pB'] else [])
    orb = {key(relab(B, a, b)) for B in base for a in SA for b in SB}
    reps = [tuple(sorted((tuple(x), tuple(y)) for x, y in r)) for r in D['reps']]
    hits = [i for i, r in enumerate(reps) if r in orb]
    assert len(hits) == 1
    rec = [json.loads(l) for l in open(f"out_{G['pat']}.jsonl") if json.loads(l)['idx'] == hits[0]]
    print(name, G['pat'], 'class', hits[0], rec)
