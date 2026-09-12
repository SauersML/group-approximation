#!/usr/bin/env python3
# dupcheck.py <sha> <Module...>  -- predict root import collisions before a wiring build.
# Parses every GroupApproximation/**/*.lean at <sha> (namespace/section stack, top-level declaration names),
# computes the root closure before and after adding <Module...>, and prints fully-qualified names declared in two
# different files of the new closure where at least one file is newly reachable. Heuristic (no elaboration).
import re, subprocess, sys
sha, mods = sys.argv[1], sys.argv[2:]
paths = subprocess.run(['git', 'ls-tree', '-r', '--name-only', sha, '--', 'GroupApproximation', 'GroupApproximation.lean'],
                       capture_output=True, text=True, check=True).stdout.split()
paths = [p for p in paths if p.endswith('.lean')]
inp = ''.join(f'{sha}:{p}\n' for p in paths)
out = subprocess.run(['git', 'cat-file', '--batch'], input=inp.encode(), capture_output=True, check=True).stdout
src, i = {}, 0
for p in paths:
    j = out.index(b'\n', i); hdr = out[i:j].split(); n = int(hdr[2]); src[p] = out[j+1:j+1+n].decode('utf-8', 'replace'); i = j + 1 + n + 1
mod = lambda p: p[:-5].replace('/', '.')
file_of = {mod(p): p for p in paths}
imp_re = re.compile(r'^import\s+(\S+)', re.M)
imports = {p: [m for m in imp_re.findall(s) if m.startswith('GroupApproximation')] for p, s in src.items()}
def closure(roots):
    seen, st = set(), [file_of[r] for r in roots if r in file_of]
    while st:
        p = st.pop()
        if p in seen: continue
        seen.add(p); st += [file_of[m] for m in imports.get(p, []) if m in file_of]
    return seen
old = closure(['GroupApproximation']); new = closure(['GroupApproximation'] + mods)
missing = [m for m in mods if m not in file_of]
if missing: print('MISSING', *missing)
decl_re = re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
                     r'(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\s+([^\s:({\[⦃]+)')
defs = {}
for p in new:
    stack = []
    for line in src[p].split('\n'):
        t = line.strip()
        if m := re.match(r'^namespace\s+(\S+)', t): stack.append(m.group(1).split('.')); continue
        if re.match(r'^(noncomputable\s+)?section\b', t): stack.append([]); continue
        if re.match(r'^end\b', t):
            if stack: stack.pop()
            continue
        m = decl_re.match(line)
        if not m or (m.group(1) and 'private' in m.group(1)) or m.group(2) == 'instance': continue
        name = m.group(3)
        if name.startswith('_root_.'): fq = name[7:]
        else: fq = '.'.join([c for s in stack for c in s] + [name])
        defs.setdefault(fq, set()).add(p)
hits = [(fq, ps) for fq, ps in defs.items() if len(ps) > 1 and any(q not in old for q in ps)]
for fq, ps in sorted(hits): print('DUP', fq, '|', ' '.join(sorted(q[len('GroupApproximation/'):] + ('' if q in old else '*') for q in ps)))
print(f'old closure {len(old)}  new closure {len(new)}  newly reachable {len(new - old)}  predicted collisions {len(hits)}')
