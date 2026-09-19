# Cone-lemma certificates for every remaining census class (remaining.json of bmw-cone-trees-2026-09-18)
# without a cone tree in that directory's trees.jsonl.gz (the 509 classes first UNSAT at radius 6, short 4):
# ctree CNF mode (radius R, short-k census CNF) -> Glucose 4 DRUP proof (gsolve.py) -> drat-trim LRAT
# (backward trimming) -> lrat2cone.py -> verify_lemmas.py.  Certificates are appended to certs.jsonl,
# one log line per class to the log.  Scratch files go to $TMPD and are deleted.
# usage: runlem.py R SHORT log [patterns...]     (env DRAT_TRIM: path of the drat-trim binary)
import json, subprocess, sys, os, time, gzip
here = os.path.dirname(os.path.abspath(__file__)); os.chdir(here)
R, SH, log = sys.argv[1:4]; pats = sys.argv[4:]
T = os.environ.get('TMPD', '/tmp'); DT = os.environ['DRAT_TRIM']
E = '../bmw-cone-trees-2026-09-18/'
cls = json.load(open(E + 'remaining.json'))
old = {(r['pat'], r['cls']) for r in map(json.loads, gzip.open(E + 'trees.jsonl.gz', 'rt'))}
done = {(r['pat'], r['cls']) for r in map(json.loads, open(log))} if os.path.exists(log) else set()
py = sys.executable
def run(cmd, **kw): return subprocess.run(['nice', '-n', '10'] + cmd, capture_output=True, text=True, **kw)
for p in pats or list(cls):
    for i in cls[p]:
        if (p, i) in old or (p, i) in done: continue
        t0 = time.time(); b = os.path.join(T, 'lem_%s_%d' % (p, i)); rec = dict(pat=p, cls=i, R=int(R), short=int(SH), ok=False)
        try:
            run([py, 'ctree.py', 'census_%s.json' % p, str(i), R, SH, '0', '0'], env=dict(os.environ, CNF=b + '.cnf'), timeout=600)
            g = run([py, 'gsolve.py', b + '.cnf', b + '.drat'], timeout=1200).stdout.split()
            rec['solver'] = ' '.join(g)
            if g and g[0] == 'UNSAT':
                d = run([DT, b + '.cnf', b + '.drat', '-L', b + '.lrat'], timeout=1200).stdout
                rec['trim'] = [l for l in d.splitlines() if 'lemmas in core' in l or l.startswith('s ')]
                c = run([py, 'lrat2cone.py', b + '.cnf', b + '.lrat', p, str(i), R, SH], timeout=1200)
                if c.returncode == 0:
                    open(b + '.cert', 'w').write(c.stdout)
                    v = run([py, 'verify_lemmas.py', b + '.cert'], timeout=1200).stdout.strip()
                    rec['check'] = v
                    if 'certificate OK' in v:
                        rec['ok'] = True; open(os.environ.get('CERTS', 'certs.jsonl'), 'a').write(c.stdout)
                else: rec['conv'] = c.stderr.strip()[-200:]
        except subprocess.TimeoutExpired as e: rec['msg'] = 'timeout ' + str(e.cmd[2:4])
        for ext in ('.cnf', '.cnf.map', '.drat', '.lrat', '.cert'):
            if os.path.exists(b + ext): os.unlink(b + ext)
        rec['sec'] = round(time.time() - t0, 1)
        open(log, 'a').write(json.dumps(rec) + '\n')
