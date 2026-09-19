# Coverage of the 994 remaining census classes: the cone trees of bmw-cone-trees-2026-09-18 plus the
# cone-lemma certificates here must be disjoint and together equal remaining.json.
# usage: coverage.py [dir of bmw-cone-trees-2026-09-18] [certs.jsonl.gz]
import sys, json, gzip, collections
E = sys.argv[1] if len(sys.argv) > 1 else '../bmw-cone-trees-2026-09-18/'
F = sys.argv[2] if len(sys.argv) > 2 else 'certs.jsonl.gz'
rem = json.load(open(E + '/remaining.json'))
R = {(p, c) for p in rem for c in rem[p]}
T = [(r['pat'], r['cls']) for r in map(json.loads, gzip.open(E + '/trees.jsonl.gz', 'rt'))]
L = [(r['pat'], r['cls']) for r in map(json.loads, gzip.open(F, 'rt'))]
assert len(set(T)) == len(T) and len(set(L)) == len(L), 'duplicate record'
assert not set(T) & set(L), 'class certified twice'
assert set(T) | set(L) == R, 'coverage mismatch: missing %s extra %s' % (sorted(R - set(T) - set(L))[:5], sorted((set(T) | set(L)) - R)[:5])
bydeg = collections.Counter()
for p, c in R: bydeg[(p[0] + '_' + p[3], (p, c) in set(L))] += 1
print('remaining %d = %d cone trees + %d cone-lemma certificates, disjoint' % (len(R), len(T), len(L)))
for d in sorted({k[0] for k in bydeg}): print('degree (%s,%s): %d trees, %d lemma certificates' % (d[0], d[2], bydeg[(d, False)], bydeg[(d, True)]))
