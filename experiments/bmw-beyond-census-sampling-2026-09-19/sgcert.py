# sgcert.py in.jsonl k R short i j f k l g out.json : turn an sgen.py hit into a certificate.
# Glucose 4 proposes a DRAT refutation; our rup checks it, trims it to a lemma core and records the input
# clauses used; rup re-checks the core. The certificate keeps only what the core uses: the squares, the
# elements (normal form "v..|h.."), the relations p*q = c (c = 0: product 1) and the lemmas (signed element
# ids). sgverify.py re-checks it with no code shared with the search.
import sys, json, os, subprocess
from sgen import group, gens_of, instance, inv
from pysat.solvers import Solver
here = os.path.dirname(os.path.abspath(__file__)); TMP = os.environ.get('TMPD', '/tmp')
a = sys.argv; r = [json.loads(l) for l in open(a[1])][int(a[2])]; R, short = int(a[3]), int(a[4])
prm = [int(x) for x in a[5:11]]; out = a[11]
G, m, n = group(r); els, cl = instance(G, gens_of(G, *prm), R, short)
f = os.path.join(TMP, 'sgc_%d.cnf' % os.getpid())
with open(f, 'w') as g:
    g.write('p cnf %d %d\n' % (len(els) - 1, len(cl)))
    for c in cl: g.write(' '.join(map(str, c)) + ' 0\n')
with Solver(name='glucose4', bootstrap_with=cl, with_proof=True) as s:
    assert not s.solve()
    with open(f + '.drat', 'w') as g:
        for line in s.get_proof(): g.write(line + '\n')
p1 = subprocess.run([os.path.join(here, 'rup'), f, f + '.drat'], capture_output=True, text=True).stdout.strip()
p2 = subprocess.run([os.path.join(here, 'rup'), f, f + '.drat.core'], capture_output=True, text=True).stdout.strip()
print(p1); print(p2); assert p1.startswith('RUP-OK') and p2.startswith('RUP-OK')
used = [cl[int(x)] for x in open(f + '.drat.core.inputs')]
lem = [list(map(int, l.split()[:-1])) for l in open(f + '.drat.core')]
ids = sorted({abs(x) for c in used + lem for x in c})
def s_(g): return ''.join('v%d' % x for x in g[0]) + '|' + ''.join('h%d' % x for x in g[1])
rel = []
for c in used:
    if len(c) == 2 and c[0] > 0: continue              # "x or x^-1": rebuilt by the verifier
    if len(c) == 2 and G.mul(els[-c[0]], els[-c[1]]) != ((), ()): continue   # "not both x, x^-1": rebuilt too
    rel.append([-c[0], -c[1], c[2] if len(c) == 3 else 0])
C = dict(pat=r['pat'], seed=r['seed'], sq=r['sq'], iA=list(G.iA), iB=list(G.iB), R=R, short=short,
         subgroup=dict(zip('i j f k l g'.split(), prm)), gens=[s_(x) for x in gens_of(G, *prm)],
         elements={str(i): s_(els[i]) for i in ids}, relations=rel, lemmas=lem, rup=[p1, p2])
json.dump(C, open(out, 'w')); print('elements', len(ids), 'relations', len(rel), 'lemmas', len(lem))
for e in ('', '.drat', '.drat.core', '.drat.inputs', '.drat.core.core', '.drat.core.inputs'):
    if os.path.exists(f + e): os.unlink(f + e)
