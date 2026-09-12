#!/usr/bin/env python3
"""purge_stale.py <clone-root> [--dry]
Delete build artifacts of GroupApproximation modules that are stale, to a fixpoint:
  (a) the module's .lean is newer than its .olean, or
  (b) the .olean is older than the .olean of any module it imports (the import was rebuilt), or
  (c) an imported GroupApproximation module has no .olean at all (it will be rebuilt, and (b) would then hold).
Lake at this pin replays such oleans silently (no Built, no Replayed line), which is a false green.
Bounded to the GroupApproximation library; Mathlib and other packages are never touched.
"""
import os, re, sys
root = sys.argv[1]; dry = '--dry' in sys.argv
src = os.path.join(root, 'GroupApproximation')
lib = os.path.join(root, '.lake', 'build', 'lib', 'lean', 'GroupApproximation')
ir  = os.path.join(root, '.lake', 'build', 'ir', 'GroupApproximation')
imp_re = re.compile(r'^\s*import\s+GroupApproximation\.([\w.]+)', re.M)
mods = {}
for dp, _, fs in os.walk(src):
    for f in fs:
        if f.endswith('.lean'):
            p = os.path.join(dp, f); rel = os.path.relpath(p, src)[:-5].replace(os.sep, '.')
            mods[rel] = p
def olean(m): return os.path.join(lib, *m.split('.')) + '.olean'
def mtime(p):
    try: return os.stat(p).st_mtime
    except FileNotFoundError: return None
imports = {}
for m, p in mods.items():
    try:
        with open(p, encoding='utf-8', errors='replace') as fh: imports[m] = imp_re.findall(fh.read(20000))
    except OSError: imports[m] = []
omt = {m: mtime(olean(m)) for m in mods}
smt = {m: mtime(p) for m, p in mods.items()}
stale, reason = set(), {}
for m in mods:
    if omt[m] is not None and smt[m] is not None and smt[m] > omt[m]: stale.add(m); reason[m] = 'source-newer'
changed = True
while changed:
    changed = False
    for m in mods:
        if m in stale or omt[m] is None: continue
        for d in imports[m]:
            if d not in mods: continue
            if d in stale or omt[d] is None or omt[d] > omt[m]:
                stale.add(m); reason[m] = f'import:{d}'; changed = True; break
suffixes = ['.olean', '.ilean', '.trace', '.hash', '.olean.hash', '.ilean.hash']
n = 0
for m in sorted(stale):
    base = os.path.join(lib, *m.split('.')); irb = os.path.join(ir, *m.split('.'))
    files = [base + s for s in suffixes] + [irb + s for s in ('.c', '.c.hash', '.trace', '.setup.json')]
    if not dry:
        for f in files:
            try: os.remove(f)
            except FileNotFoundError: pass
    n += 1
by = {}
for m in stale: by[reason[m].split(':')[0]] = by.get(reason[m].split(':')[0], 0) + 1
print(f"purged {n} stale artifact sets ({'DRY RUN, ' if dry else ''}source-newer={by.get('source-newer',0)}, import-newer={by.get('import',0)}) of {sum(1 for m in mods if omt[m] is not None)} oleans")
