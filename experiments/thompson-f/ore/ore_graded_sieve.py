import gzip, json, sys, collections
sys.path.insert(0, '.')
from ore_linalg import guba_set
S = guba_set(2, 2)
assert [tuple(w) for w in S] == [(0,0),(0,1),(0,2),(0,3),(1,1),(1,2),(1,3),(2,2),(2,3)], S
nu0 = [sum(1 for x in w if x == 0) for w in S]
lev = {e: sum(1 << i for i in range(9) if nu0[i] == e) for e in (0, 1, 2)}
uns = set(tuple(p) for p in json.load(gzip.open('s35_unsolved.json.gz'))['unsolved'])
assert len(uns) == 94329, len(uns)
def comp(m, e): return m & lev[e]
def top(m):
    for e in (2, 1, 0):
        if comp(m, e): return comp(m, e), e
def bot(m):
    for e in (0, 1, 2):
        if comp(m, e): return comp(m, e), e
def bihom(m): return sum(1 for e in (0,1,2) if comp(m, e)) == 1
def status(a, b):
    if a == b: return 'equal'
    p = (min(a, b), max(a, b))
    return 'unsolved' if p in uns else 'solved'
C = collections.Counter(); core = collections.Counter(); ex = []
for (a, b) in sorted(uns):
    ta, ea = top(a); tb, eb = top(b); ba, fa = bot(a); bb, fb = bot(b)
    st, sb = status(ta, tb), status(ba, bb)
    kind = 'bihomogeneous' if bihom(a) and bihom(b) else 'mixed'
    C[(kind, st, sb)] += 1
    if kind == 'bihomogeneous': core[(top(a)[1], top(b)[1])] += 1
    if kind == 'mixed' and 'unsolved' in (st, sb) and len(ex) < 5: ex.append((a, b, ta, tb, ba, bb, st, sb))
print('SIEVE', {'|'.join(k): v for k, v in sorted(C.items())})
print('CORE_levels', dict(core))
print('EXAMPLES', ex)
# component pairs of type (x0*l, q) with l nonmonomial: census status
cnt = collections.Counter()
for m1 in range(1, 512):
    if not (bihom(m1) and top(m1)[1] == 1 and bin(m1).count('1') >= 2): continue
    for m2 in range(1, 512):
        if bihom(m2) and top(m2)[1] == 0:
            cnt[status(m1, m2)] += 1
print('L1_vs_L0_nonmonomial_pairs', dict(cnt))
print('DONE')
