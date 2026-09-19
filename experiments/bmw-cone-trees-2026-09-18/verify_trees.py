# Check every cone-tree certificate in a packed file (pack_trees.py) with the independent checker
# verify_cone.py (same directory), one subprocess per class; prints one line per class and a summary.
# usage: verify_trees.py trees.jsonl.gz
import sys, json, gzip, os, subprocess, tempfile
here = os.path.dirname(os.path.abspath(__file__))
ok = bad = 0
for line in gzip.open(sys.argv[1], 'rt'):
    r = json.loads(line)
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as t:
        t.write(json.dumps(dict(cls=r['cls'], tree=r['tree'])) + '\n'); name = t.name
    p = subprocess.run([sys.executable, os.path.join(here, 'verify_cone.py'), 'census_%s.json' % r['pat'],
                        str(r['cls']), name], capture_output=True, text=True)
    os.unlink(name)
    out = (p.stdout.strip().splitlines() or [''])[-1]
    good = p.returncode == 0 and 'certificate OK' in out
    ok += good; bad += not good
    print(r['pat'], r['cls'], 'R=%d' % r['R'], out if good else 'FAILED ' + (p.stderr.strip().splitlines() or [''])[-1], flush=True)
print('summary: %d certificates OK, %d failed' % (ok, bad))
