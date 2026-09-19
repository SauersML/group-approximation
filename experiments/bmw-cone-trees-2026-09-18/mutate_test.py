# Sanity test of verify_cone.py: it must accept a certificate and reject corrupted copies of it.
# Mutations of the first leaf of tree_40_40_818: (1) drop its first product step; (2) replace the
# product in its first step by a different element; (3) replace its final pair by (x, x); (4) split the
# root on the letter v0, which is not in Gamma^+.  Each must be rejected.
# usage: mutate_test.py trees.jsonl.gz
import json, subprocess, sys, os, copy, tempfile, gzip
here = os.path.dirname(os.path.abspath(__file__))
rec = next(r for r in map(json.loads, gzip.open(sys.argv[1], 'rt')) if (r['pat'], r['cls']) == ('40_40', 818))
def leaf(T):
    while T[0] == 'split': T = T[2]
    return T
def run(tree):
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as t:
        t.write(json.dumps(dict(cls=818, tree=tree)) + '\n'); name = t.name
    p = subprocess.run([sys.executable, os.path.join(here, 'verify_cone.py'), 'census_40_40.json', '818', name],
                       capture_output=True, text=True)
    os.unlink(name)
    return p.returncode, (p.stdout.strip().splitlines() or p.stderr.strip().splitlines() or [''])[-1]
muts = {}
T = copy.deepcopy(rec['tree']); L = leaf(T); del L[2][0]; muts['drop first step'] = T
T = copy.deepcopy(rec['tree']); L = leaf(T); L[2][0][0] = L[2][1][0]; muts['wrong product'] = T
T = copy.deepcopy(rec['tree']); L = leaf(T); L[1] = [L[1][0], L[1][0]]; muts['no contradiction'] = T
T = copy.deepcopy(rec['tree']); T[1] = 'v0'; muts['odd split element'] = T
rc, out = run(rec['tree']); print('original:', 'accepted' if rc == 0 else 'REJECTED', '|', out)
bad = rc != 0
for k, t in muts.items():
    rc, out = run(t); print('%-18s' % k, 'rejected' if rc else 'ACCEPTED', '|', out); bad |= rc == 0
print('mutation test', 'FAILED' if bad else 'passed')
