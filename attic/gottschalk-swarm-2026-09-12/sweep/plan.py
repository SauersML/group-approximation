"""Plan the coordinator sweep: live path, rescue path (attic), skip, or defer, per classified path.
Writes stage/<repo path> copies, specs.txt (gkland specs), acks.txt (GK_ACK), plan.tsv."""
import os, subprocess, shutil, re, sys
REPO = '/Users/user/nonsofic_existence'
S = os.path.dirname(os.path.abspath(__file__))
STG = os.path.join(S, 'stage')
ATTIC = 'attic/sweep-2026-09-12/'
MINAGE = float(os.environ.get('MINAGE', '0.5'))
os.chdir(REPO)

def git(*a, check=True):
    return subprocess.run(['git', *a], capture_output=True, check=check).stdout

hdr = open(os.path.join(S, 'classes.tsv')).readline().split()
TIP = hdr[2]
rows = [l.rstrip('\n').split('\t') for l in open(os.path.join(S, 'classes.tsv')) if not l.startswith('#')]
merges = {}
mp = os.path.join(S, 'merges.tsv')
if os.path.exists(mp):
    for l in open(mp):
        if not l.startswith('#'):
            f = l.rstrip('\n').split('\t')
            merges[f[0]] = f

def on_tip(p):
    return subprocess.run(['git', 'cat-file', '-e', f'{TIP}:{p}'], capture_output=True).returncode == 0

def tip_blob(p):
    r = subprocess.run(['git', 'rev-parse', '-q', '--verify', f'{TIP}:{p}'], capture_output=True, text=True)
    return r.stdout.strip() or None

RESCUE_PREFIX = ('notes/nm-swarm/', 'metadata/', 'tools/', '.github/', 'GroupApproximation/', 'wip/', 'Palomar/', 'scripts/', 'bin/', 'vendor/')
LIVE_PREFIX = ('research/', 'experiments/', 'notes/', 'docs/')

already_merged = {}   # (path, local blob) -> commit that landed its merge
lm = os.path.join(S, 'landed-merges.tsv')
if os.path.exists(lm):
    for l in open(lm):
        if not l.startswith('#') and l.strip():
            f = l.rstrip('\n').split('\t')
            already_merged[(f[0], f[1])] = f[3]

plan = {}   # repo path -> dict(action, src, ack, why, orig)
for cls, xy, p, w, h, o, age in rows:
    if cls.startswith('SKIP'):
        continue
    a = float(age)
    if a < MINAGE:
        plan[p] = dict(action='DEFER', why=f'fresh {a}h', orig=p); continue
    cur = git('hash-object', '--no-filters', '--', p, check=False).decode().strip()
    if cur != w:
        plan[p] = dict(action='DEFER', why='changed since classify', orig=p); continue
    if cls in ('LAND_NEW', 'LAND_EDIT') and p.startswith(LIVE_PREFIX) and not p.startswith(RESCUE_PREFIX):
        plan[p] = dict(action='LIVE', src=p, ack=(o if cls == 'LAND_EDIT' else None), why=cls, orig=p)
    elif cls == 'RESCUE_DIVERGED' and p.startswith('research/'):
        m = merges.get(p)
        W_lines = set(open(p, 'rb').read().splitlines())
        O_lines = set(git('cat-file', 'blob', o).splitlines())
        if (p, w) in already_merged:
            plan[p] = dict(action='SKIP', why=f'this local copy was already merged onto main in {already_merged[(p, w)]}', orig=p)
        elif W_lines <= O_lines:
            plan[p] = dict(action='SKIP', why='every local line is already on main (subsumed)', orig=p)
        elif m is None:
            plan[p] = dict(action='DEFER', why='no merge computed', orig=p)
        elif m[1] == 'CLEAN' and 'M==O' in m[4]:
            plan[p] = dict(action='SKIP', why='merge equals main', orig=p)
        elif m[1] == 'CLEAN':
            plan[p] = dict(action='LIVE', src=os.path.join(S, 'merged', p), ack=o, why=f'3-way merge base {m[2]} ({m[4]})', orig=p)
        else:
            plan[p] = dict(action='RESCUE', src=p, why=f'merge {m[1]}', orig=p)
    else:
        plan[p] = dict(action='RESCUE', src=p, why=cls, orig=p)

def frontmatter(path):
    t = open(path, encoding='utf-8', errors='replace').read()
    if not t.startswith('---\n'):
        return {}
    end = t.find('\n---', 4)
    fm, cur, out = t[4:end].splitlines(), None, {}
    for line in fm:
        mk = re.match(r'^([a-z_]+):\s*(.*)$', line)
        if mk:
            cur, v = mk.group(1), mk.group(2).strip()
            out.setdefault(cur, [])
            if v.startswith('['):
                out[cur] += [x.strip() for x in v.strip('[]').split(',') if x.strip()]
            elif v:
                out[cur].append(v)
            continue
        mi = re.match(r'^\s+-\s+(.*)$', line)
        if mi and cur:
            out[cur].append(mi.group(1).strip())
    return out

def is_node(p):
    return re.match(r'^research/[^/]+\.md$', p) and p != 'research/FRONTIER.md'

# node checks, iterated to a fixpoint
changed = True
while changed:
    changed = False
    live = {p for p, d in plan.items() if d['action'] == 'LIVE'}
    live_ids = {os.path.basename(p)[:-3] for p in live if is_node(p)}
    fms = {p: frontmatter(plan[p]['src']) for p in live if is_node(p)}
    live_route_targets = {fm.get('target', [''])[0] for fm in fms.values() if fm.get('kind', [''])[0] == 'route'}
    for p in sorted(live):
        if not is_node(p):
            continue
        fm, bad = fms[p], None
        orig_fm_same = 'fm-same' in plan[p]['why']
        for art in fm.get('artifacts', []):
            if re.match(r'^[0-9a-f]{7,40}:', art):
                continue
            if not (on_tip(art) or art in live):
                bad = f'artifact {art} not on main or in live set'
        for key in ('requires', 'target', 'distinct_from', 'refuted_by', 'invalidates'):
            for r in fm.get(key, []):
                if not (on_tip(f'research/{r}.md') or r in live_ids):
                    bad = f'{key} {r} not on main or in live set'
        if not bad and not orig_fm_same and fm.get('kind', [''])[0] == 'route':
            tgt = fm.get('target', [''])[0]
            if on_tip(f'research/{tgt}.md'):
                reqs = fm.get('requires', [])
                if all(on_tip(f'research/{r}.md') or r in live_route_targets for r in reqs):
                    bad = f'route could establish pre-existing claim {tgt}; not asserting it on main for another session'
        if bad:
            plan[p] = dict(action='RESCUE', src=plan[p]['src'], why=bad, orig=p)
            changed = True

# rescue paths and staging
if os.path.isdir(STG):
    shutil.rmtree(STG)
specs, acks, out = [], [], []
for p in sorted(plan):
    d = plan[p]
    if d['action'] in ('LIVE', 'RESCUE'):
        dst = p if d['action'] == 'LIVE' else ATTIC + p + ('.txt' if p.endswith('.lean') else '')
        src = d['src']
        blob = git('hash-object', '--no-filters', '--', src).decode().strip()
        tb = tip_blob(dst)
        if d['action'] == 'RESCUE' and tb and tb != blob:
            dst = dst + '.v2'; tb = tip_blob(dst)
        if tb == blob:
            d['action'] = 'SKIP'; d['why'] += ' (target already holds this content)'
        else:
            sp = os.path.join(STG, dst)
            os.makedirs(os.path.dirname(sp), exist_ok=True)
            shutil.copyfile(src, sp)
            specs.append(f'{dst}@{sp}')
            if d['action'] == 'LIVE' and d.get('ack'):
                acks.append(f'{dst}={d["ack"]}')
        d['dst'] = dst
    out.append((d['action'], p, d.get('dst', '-'), d['why']))
open(os.path.join(S, 'specs.txt'), 'w').write('\n'.join(specs) + '\n')
open(os.path.join(S, 'acks.txt'), 'w').write(' '.join(acks))
with open(os.path.join(S, 'plan.tsv'), 'w') as fh:
    fh.write(f'# tip {TIP}\n')
    for r in out:
        fh.write('\t'.join(r) + '\n')
import collections
print(collections.Counter(r[0] for r in out))
for r in out:
    if r[0] != 'LIVE' or 'merge' in r[3]:
        print('\t'.join(r))
