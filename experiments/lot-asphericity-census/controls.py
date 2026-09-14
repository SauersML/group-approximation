#!/usr/bin/env python3
"""Calibration of lot.py against pinned examples.  Soundness controls must come out as
stated, otherwise the checker is broken and nothing it certifies can be used."""
import itertools, json
from lot import *

ok = []
def expect(cond, msg):
    ok.append(bool(cond)); print(('PASS ' if cond else 'FAIL ') + msg, flush=True)

# C1. Trefoil Wirtinger presentation as an injective labelled oriented circle.  Not
# aspherical: one relator is a consequence of the others (arXiv:1212.1943, Sec. 1).
C = [(0, 2, 1), (1, 0, 2), (2, 1, 0)]
R = [rel(e) for e in C]
vs = [list(v) for v in itertools.product((-2, -1, 0, 1, 2), repeat=3) if any(v)]
expect(test_itest(3, C, rels=R, vs=vs) is None, 'C1 I-test fails on the trefoil circle')
expect(test_weight(3, C, rels=R) is None, 'C1 weight test fails on the trefoil circle')

# C2. <x,y | [x,y], [x,y]>: a repeated relator gives pi_2 != 0.
R2 = [[(0, 1), (1, 1), (0, -1), (1, -1)]] * 2
vs2 = [list(v) for v in itertools.product((-2, -1, 0, 1, 2), repeat=2) if any(v)]
expect(test_itest(2, None, rels=R2, vs=vs2) is None, 'C2 I-test fails on a repeated relator')
expect(test_weight(2, None, rels=R2) is None, 'C2 weight test fails on a repeated relator')

# C3. Barmak--Minian Example 3.1: <x,y | x^3 y x y> satisfies the I-test for v = (1,-2)
# but no weight function satisfies the weight test.
R3 = [[(0, 1), (0, 1), (0, 1), (1, 1), (0, 1), (1, 1)]]
expect(test_itest(2, None, rels=R3, vs=[[1, -2]]) is not None, 'C3 I-test passes on x^3yxy')
expect(test_weight(2, None, rels=R3) is None, 'C3 weight test fails on x^3yxy')

# C4. Barmak--Minian Example 2.3 with v = (1,0,-1,2), column order 2,3,1, row order 2,4,1.
x, y, z, w = 0, 1, 2, 3
R4 = [[(x, 1), (x, 1), (y, 1), (y, 1), (z, 1), (z, 1)],
      [(x, 1), (y, 1), (x, -1), (z, 1), (y, 1), (z, -1)],
      [(w, 1), (w, 1), (x, -1), (w, -1), (z, 1)]]
v4 = [1, 0, -1, 2]
M4 = weight_matrix(4, R4, v4)
expect([sorted(M4[0][j]) for j in range(3)] == [[-1, 0], [0, 0], [-3]], 'C4 weight matrix row x matches the paper')
expect(verify_itest(4, R4, v4, [1, 3, 0], [1, 2, 0]), 'C4 paper orderings verify')
expect(test_itest(4, None, rels=R4, vs=[v4]) is not None, 'C4 greedy I-test passes')

# C5. Huck--Rosebrock Figure 1 (via arXiv:1912.12512 Fig. 1): the path g-a-b-c-d-e-f with
# labels f,d,e,b,c,g is reduced, injective (so aspherical) and fails the weight test for
# every orientation.
g, a, b, c, d, e, f = range(7)
path = [(g, a), (a, b), (b, c), (c, d), (d, e), (e, f)]
labs = [f, d, e, b, c, g]
wpass = 0
for orient in itertools.product((0, 1), repeat=6):
    E = [(u, l, v) if o == 0 else (v, l, u) for (u, v), l, o in zip(path, labs, orient)]
    if orient == (0,) * 6:
        expect(is_reduced(7, E), 'C5 Figure 1 LOT is reduced')
        expect(test_inj(7, E) is not None, 'C5 Figure 1 LOT is injective')
    if test_weight(7, E) is not None: wpass += 1
expect(wpass == 0, 'C5 weight test fails on all 64 orientations (passes: %d)' % wpass)

# C6. Reductions: a single edge labelled by an endpoint compresses to a point; the survey
# Figure 2 LOT <a,b,c,d,e | ac=cb, bd=dc, db=bc, da=ae> has diameter 4.
expect(reduce_lot(2, [(0, 0, 1)])[0] == 1, 'C6 compress [a,a,b] to one vertex')
expect(reduce_lot(3, [(0, 2, 1), (1, 0, 2)])[0] == 3, 'C6 path with both leaves as labels is already reduced')
expect(reduce_lot(4, [(0, 2, 1), (1, 0, 2), (2, 1, 3)])[0] == 3, 'C6 boundary reduction removes leaf 3')
expect(reduce_lot(4, [(1, 3, 0), (2, 3, 0), (0, 1, 3)])[0] == 3, 'C6 interior reduction folds 1 and 2')
S = [(0, 2, 1), (1, 3, 2), (3, 1, 2), (3, 0, 4)]
red, name, cert = certify(5, S)
print('INFO C6 survey Figure 2 LOT: reduced', red, 'first test', name, json.dumps(cert))

# C7. Barmak--Minian Example 4.5: path 1-2-3-4-5, labels 4,1,5,1, deforestable for its
# orientation, with I and T both cyclic.  Report the orientations passing the I-test.
P = [(0, 1), (1, 2), (2, 3), (3, 4)]; L = [3, 0, 4, 0]
hits = []
for orient in itertools.product((0, 1), repeat=4):
    E = [(u, l, v) if o == 0 else (v, l, u) for (u, v), l, o in zip(P, L, orient)]
    ci = cyclomatic(5, [(l, t) for (i, l, t) in E]); ct = cyclomatic(5, [(l, i) for (i, l, t) in E])
    if ci >= 1 and ct >= 1 and test_itest(5, E) is not None: hits.append(orient)
expect(len(hits) > 0, 'C7 some orientation has cyclic I and T and passes the I-test: %s' % hits)

print('CONTROLS', 'ALL_PASS' if all(ok) else 'SOME_FAIL', '%d/%d' % (sum(ok), len(ok)))
