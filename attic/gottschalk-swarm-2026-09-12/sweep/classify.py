import os, sys, subprocess, collections, time
REPO = '/Users/user/nonsofic_existence'
S = os.path.dirname(os.path.abspath(__file__))
os.chdir(REPO)
TIP = subprocess.check_output(['git', 'rev-parse', 'origin/main'], text=True).strip()

def run(args, inp=None):
    return subprocess.run(args, input=inp, capture_output=True, check=True).stdout

# 1. status rows
data = open(os.path.join(S, 'status.z'), 'rb').read().split(b'\0')
rows, i = {}, 0
while i < len(data):
    e = data[i]
    if not e:
        i += 1; continue
    xy, p = e[:2].decode(), e[3:].decode('utf-8', 'surrogateescape')
    if xy[0] in 'RC':
        i += 1
    rows[p] = xy; i += 1
# 2. paths touched by unpushed local commits
for p in run(['git', 'diff', '--name-only', '-z', TIP + '...HEAD']).split(b'\0'):
    if p:
        rows.setdefault(p.decode('utf-8', 'surrogateescape'), 'LC')
paths = sorted(rows)

# 3. working-tree blobs
reg = [p for p in paths if os.path.isfile(p) and not os.path.islink(p)]
W = dict(zip(reg, run(['git', 'hash-object', '--no-filters', '--stdin-paths'], ('\n'.join(reg) + '\n').encode()).decode().split()))

def batch_check(ref):
    out = run(['git', 'cat-file', '--batch-check=%(objectname) %(objecttype)'], ''.join(f'{ref}:{p}\n' for p in paths).encode()).decode().splitlines()
    res = {}
    for p, line in zip(paths, out):
        parts = line.split()
        res[p] = parts[0] if len(parts) == 2 and parts[1] == 'blob' else None
    return res
O, H = batch_check(TIP), batch_check('HEAD')

# 4. every object and path ever on main
t = time.time()
hist_sha, hist_path = set(), set()
proc = subprocess.Popen(['git', 'rev-list', '--objects', TIP], stdout=subprocess.PIPE)
for line in proc.stdout:
    parts = line.rstrip(b'\n').split(b' ', 1)
    hist_sha.add(parts[0].decode())
    if len(parts) == 2:
        hist_path.add(parts[1].decode('utf-8', 'surrogateescape'))
proc.wait()
print('rev-list objects', len(hist_sha), 'secs', round(time.time() - t))

LEAN_GLOBAL = ('lakefile', 'lean-toolchain', 'lake-manifest.json', 'GroupApproximation.lean')
now = time.time()
out = []
for p in paths:
    w, o, h = W.get(p), O[p], H[p]
    if w is None:
        cls = 'SKIP_NOFILE' if not os.path.islink(p) else 'SKIP_SYMLINK'
    elif w == o:
        cls = 'SKIP_ONMAIN'
    elif w in hist_sha:
        cls = 'SKIP_STALE'
    elif o is None and p in hist_path:
        cls = 'RESCUE_DELETED_ON_MAIN'
    elif o is None:
        cls = 'LAND_NEW'
    elif o == h:
        cls = 'LAND_EDIT'
    else:
        cls = 'RESCUE_DIVERGED'
    if cls.startswith('LAND') and (p.endswith('.lean') or p.startswith('.github/') or p.startswith(LEAN_GLOBAL)):
        cls = cls.replace('LAND', 'RESCUE_BUILD')
    age_h = (now - os.path.getmtime(p)) / 3600 if os.path.lexists(p) else -1
    out.append((cls, rows[p], p, w or '-', h or '-', o or '-', f'{age_h:.1f}'))
with open(os.path.join(S, 'classes.tsv'), 'w') as fh:
    fh.write(f'# tip {TIP}\n')
    for r in out:
        fh.write('\t'.join(r) + '\n')
c = collections.Counter(r[0] for r in out)
print('tip', TIP[:10], 'paths', len(out)); print(dict(c))
d = collections.Counter((r[0], r[2].split('/')[0] if '/' in r[2] else '(root)', os.path.splitext(r[2])[1]) for r in out if not r[0].startswith('SKIP'))
for k, v in sorted(d.items(), key=lambda x: -x[1])[:40]:
    print(v, k)
fresh = [r for r in out if not r[0].startswith('SKIP') and 0 <= float(r[6]) < 2]
print('non-skip modified within 2h:', len(fresh))
for r in fresh[:25]:
    print('  ', r[0], r[6] + 'h', r[2])
