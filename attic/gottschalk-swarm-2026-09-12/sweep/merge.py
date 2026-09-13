import os, subprocess, tempfile
REPO = '/Users/user/nonsofic_existence'
S = os.path.dirname(os.path.abspath(__file__))
os.chdir(REPO)
MD = os.path.join(S, 'merged')

def git(*a, inp=None, check=True):
    return subprocess.run(['git', *a], input=inp, capture_output=True, check=check).stdout

tip = open(os.path.join(S, 'classes.tsv')).readline().split()[2]
rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(S, 'classes.tsv')) if not l.startswith('#')]
cands = [r for r in rows if r[0] == 'RESCUE_DIVERGED' and r[2].startswith('research/') and float(r[6]) >= 0.5]

def fm(b):
    t = b.decode('utf-8', 'replace')
    if not t.startswith('---\n'):
        return None
    end = t.find('\n---', 4)
    return t[:end] if end > 0 else None

out = []
for cls, xy, p, w, h, o, age in cands:
    W = open(p, 'rb').read()
    O = git('cat-file', 'blob', o)
    commits = git('rev-list', '--max-count=300', tip, '--', p).decode().split()
    wl = set(W.splitlines())
    best, bscore = None, None
    seen = set()
    for c in commits:
        r = subprocess.run(['git', 'rev-parse', '--verify', '-q', f'{c}:{p}'], capture_output=True)
        b = r.stdout.decode().strip()
        # the tip blob is never a base: base == main makes the merge return the local copy wholesale
        if not b or b in seen or b == o:
            continue
        seen.add(b)
        B = git('cat-file', 'blob', b)
        score = len(wl.symmetric_difference(B.splitlines()))
        if bscore is None or score < bscore:
            best, bscore = b, score
    if best is None:
        out.append((p, 'NOBASE', '-', '-', '-', age)); continue
    B = git('cat-file', 'blob', best)
    with tempfile.TemporaryDirectory() as td:
        fw, fb, fo = (os.path.join(td, n) for n in ('w', 'b', 'o'))
        open(fw, 'wb').write(W); open(fb, 'wb').write(B); open(fo, 'wb').write(O)
        r = subprocess.run(['git', 'merge-file', '-p', '-L', 'local', '-L', 'base', '-L', 'main', fw, fb, fo], capture_output=True)
        M, nconf = r.stdout, r.returncode
    status = 'CLEAN' if nconf == 0 else f'CONFLICT{nconf}'
    if nconf == 0:
        dst = os.path.join(MD, p)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, 'wb').write(M)
    same_o = 'M==O' if M == O else ('M==W' if M == W else 'M!=O')
    fmchg = 'fm-same' if fm(M) == fm(O) else 'fm-CHANGED'
    out.append((p, status, best[:10], str(bscore), same_o + ' ' + fmchg, age))
with open(os.path.join(S, 'merges.tsv'), 'w') as fh:
    fh.write(f'# tip {tip}\n')
    for r in out:
        fh.write('\t'.join(r) + '\n')
        print('\t'.join(r))
