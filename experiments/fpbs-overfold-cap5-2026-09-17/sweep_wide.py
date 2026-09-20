"""Beam sweep over the j=2 Cayley levels with V > 256 that the w17 census
(census_cayley24_j2_cap3.txt) skipped.

For each level:
  1. export it (../fpbs-overfold-exact-c-2026-09-17/export.py) to wide/;
  2. law: lawful-only beam with a width larger than any level, so the search is
     exhaustive whenever no level is truncated (flag EXACT);
  3. all-seed beam (width B, rng seed r) up to law seeds.  A goal below law is
     a certified counterexample (the witness is re-verified literally by beamw).

Usage: python3 sweep_wide.py B r [threads]
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EXA = os.path.join(HERE, '..', 'fpbs-overfold-exact-c-2026-09-17')
CENSUS = os.path.join(EXA, 'census_cayley24_j2_cap3.txt')
WIDE = os.path.join(HERE, 'wide')
LAWB = 1000000


def run(cmd, env):
    return subprocess.run(cmd, capture_output=True, text=True, env=env).stdout


def parse(out, B):
    goal = None
    trunc = False
    recheck = None
    wit = []
    for line in out.splitlines():
        m = re.match(r'level (\d+) GOAL', line)
        if m:
            goal = int(m.group(1))
        m = re.search(r'kept (\d+) states', line)
        if m and int(m.group(1)) >= B:
            trunc = True
        if line.startswith('RECHECK'):
            recheck = line.split()[-1]
        m = re.match(r'\s+(\d+) (\d+) (lawful|overfold)', line)
        if m:
            wit.append(m.group(3))
    return goal, trunc, recheck, wit


def main():
    B = int(sys.argv[1])
    r = int(sys.argv[2])
    env = dict(os.environ)
    if len(sys.argv) > 3:
        env['OMP_NUM_THREADS'] = sys.argv[3]
    os.makedirs(WIDE, exist_ok=True)
    for line in open(CENSUS):
        if 'skipped' not in line:
            continue
        perms = re.findall(r'\(([0-9, ]+)\)', line)
        pa, pb = [p.replace(' ', '') for p in perms[:2]]
        name = 'j2_' + pa.replace(',', '') + '_' + pb.replace(',', '') + '.txt'
        path = os.path.join(WIDE, name)
        if not os.path.exists(path):
            txt = run(['python3', os.path.join(EXA, 'export.py'), '2', pa, pb,
                       'cayley'], env)
            open(path, 'w').write(txt)
        V, n = open(path).readline().split()
        law, ltr, lre, _ = parse(run([os.path.join(HERE, 'beamw'), path, '15',
                                      str(LAWB), '1', 'law'], env), LAWB)
        lawtag = 'EXACT' if not ltr else 'beam'
        if law is None:
            print(f'({pa}) ({pb}) n {n} V {V} law > 15 ?', flush=True)
            continue
        deep, dtr, dre, wit = parse(run([os.path.join(HERE, 'beamw'), path,
                                         str(law), str(B), str(r)], env), B)
        over = wit.count('overfold')
        if deep is None:
            verdict = f'beam found no witness within law = {law}'
        elif deep < law:
            verdict = f'COUNTEREXAMPLE deep <= {deep} < law {law} recheck {dre}'
        else:
            verdict = f'beam deep = {deep} = law (overfold seeds in witness {over})'
        print(f'({pa}) ({pb}) n {n} V {V} law {law} [{lawtag} recheck {lre}] '
              f'B {B} rng {r}: {verdict}', flush=True)


if __name__ == '__main__':
    main()
