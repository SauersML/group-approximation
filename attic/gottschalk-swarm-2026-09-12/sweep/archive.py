"""Plan the end-of-swarm archive: every scratchpad file whose content is not already on main
goes under attic/gottschalk-swarm-2026-09-12/. Writes stage-archive/, specs-archive.txt, archive-plan.tsv."""
import os, re, shutil, subprocess, sys
REPO = '/Users/user/nonsofic_existence'
SP = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
S = os.path.join(SP, 'sweep')
STG = os.path.join(S, 'stage-archive')
ATT = 'attic/gottschalk-swarm-2026-09-12/'
MAXFILE = 1 << 20
os.chdir(REPO)

def git(*a, inp=None):
    return subprocess.run(['git', *a], input=inp, capture_output=True, check=True).stdout

tip = git('ls-remote', 'origin', 'refs/heads/main').split()[0].decode()
if subprocess.run(['git', 'cat-file', '-e', tip], capture_output=True).returncode:
    subprocess.run(['git', 'fetch', '-q', 'origin', 'main'], check=True)
on_main = {l.split()[2] for l in git('ls-tree', '-r', tip).decode('utf-8', 'surrogateescape').splitlines() if l.split()[1] == 'blob'}

SKIP_DIRS = ('sweep/stage/', 'sweep/stage-archive/', 'sweep/merged/', 'sweep/pass1/merged/')
SKIP_NAME = re.compile(r'(^|/)(tmp\.[^/]*|o\.tmp|status\.z|tree\d*\.txt|FRONTIER[^/]*\.md|\.DS_Store|index|index\.lock|[^/]*\.pyc)$|(^|/)(tmp\.[^/]+|__pycache__)/')
# key-shaped tokens only: kebab-case node ids (mask-..., risk-...) are all lowercase and must not trip it
SECRET = re.compile(rb'BEGIN [A-Z ]*PRIVATE KEY|ghp_[A-Za-z0-9]{20,}|(?<![A-Za-z0-9])sk-(?=[A-Za-z0-9_-]*[0-9])(?=[A-Za-z0-9_-]*[A-Z])[A-Za-z0-9_-]{20,}|AKIA[0-9A-Z]{16}|xox[bap]-[A-Za-z0-9-]{10,}')

cands, plan = [], []
for root, dirs, files in os.walk(SP):
    for f in files:
        rel = os.path.relpath(os.path.join(root, f), SP)
        if rel.startswith(SKIP_DIRS) or SKIP_NAME.search(rel):
            plan.append(('SKIP', rel, '-', '-', 'derived or private index')); continue
        cands.append(rel)
blobs = git('hash-object', '--no-filters', '--stdin-paths', inp=('\n'.join(os.path.join(SP, c) for c in cands) + '\n').encode()).decode().split()
if os.path.isdir(STG):
    shutil.rmtree(STG)
specs, total = [], 0
for rel, b in zip(cands, blobs):
    src = os.path.join(SP, rel)
    size = os.path.getsize(src)
    if b in on_main:
        plan.append(('SKIP', rel, '-', str(size), 'content already on main')); continue
    head = open(src, 'rb').read(MAXFILE + 1)
    if size > MAXFILE:
        plan.append(('HOLD', rel, '-', str(size), 'over 1 MiB')); continue
    if b'\0' in head[:8192]:
        plan.append(('HOLD', rel, '-', str(size), 'binary')); continue
    if SECRET.search(head):
        plan.append(('HOLD', rel, '-', str(size), 'secret-like token')); continue
    dst = ATT + rel + ('.txt' if rel.endswith('.lean') else '')
    sp = os.path.join(STG, dst)
    os.makedirs(os.path.dirname(sp), exist_ok=True)
    shutil.copyfile(src, sp)
    specs.append(f'{dst}@{sp}')
    total += size
    plan.append(('ARCHIVE', rel, dst, str(size), 'not on main'))
open(os.path.join(S, 'specs-archive.txt'), 'w').write('\n'.join(specs) + '\n')
with open(os.path.join(S, 'archive-plan.tsv'), 'w') as fh:
    fh.write(f'# tip {tip}\n')
    for r in plan:
        fh.write('\t'.join(r) + '\n')
import collections
print('tip', tip, collections.Counter(r[0] for r in plan), f'archive bytes {total}')
for r in plan:
    if r[0] == 'HOLD':
        print('\t'.join(r))
