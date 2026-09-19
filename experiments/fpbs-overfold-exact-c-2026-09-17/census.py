"""Exact law_j and a lower bound on deep_j for the Cayley levels of
local_cayley24_j1.txt, using the C solver deep.c.

Usage: python3 census.py j cap timeout_s [laws] > census_out.txt
(optional laws: comma list; only levels with these law values are searched)
For each level: law is computed exactly (lawful seeds only, which is cheap);
then all seeds are searched up to min(law - 1, cap) seeds.  The verdict is
  deep = law        if the all-seed search is complete to law - 1,
  deep >= k         if it was complete to k < law - 1 (cap or timeout),
  COUNTEREXAMPLE    if the goal is reached below law.
"""
import os
import re
import subprocess
import sys
import tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from export import instance_text, cayley  # noqa: E402

SRC = os.path.join(HERE, '..', 'fpbs-overfold-relative-rank-2026-09-17',
                   'local_cayley24_j1.txt')
DEEP = os.path.join(HERE, 'deep')


def run(path, level, law, timeout):
    args = [DEEP, path, str(level)] + (['law'] if law else [])
    out = ''
    try:
        out = subprocess.run(args, capture_output=True, text=True,
                             timeout=timeout).stdout
    except subprocess.TimeoutExpired as e:
        out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or '')
    goal = re.search(r'level (\d+) GOAL', out)
    done = [int(k) for k in re.findall(r'level (\d+): no goal', out)]
    return (int(goal.group(1)) if goal else None), (max(done) if done else 0)


def main():
    j, cap, timeout = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    only = set(int(x) for x in sys.argv[4].split(',')) if len(sys.argv) > 4 else None
    seen = set()
    for line in open(SRC):
        tup = re.findall(r'\(([\d, ]+)\)', line)
        al = tuple(int(x) for x in tup[0].split(','))
        be = tuple(int(x) for x in tup[1].split(','))
        PA, PB = cayley(al, be, 10 ** 6)
        key = (tuple(PA), tuple(PB))
        if key in seen:
            continue
        seen.add(key)
        text = instance_text(PA, PB, j)
        V = int(text.split()[0])
        if V > 256:
            print(al, be, 'n', len(PA), 'V', V, 'skipped (V > 256)', flush=True)
            continue
        fd, path = tempfile.mkstemp(suffix='.txt')
        with os.fdopen(fd, 'w') as f:
            f.write(text)
        law, _ = run(path, 40, True, timeout)
        if law is None or law <= 1:
            print(al, be, 'n', len(PA), 'law', law, 'trivial', flush=True)
            os.unlink(path)
            continue
        if only is not None and law not in only:
            os.unlink(path)
            continue
        lim = min(law - 1, cap)
        g, done = run(path, lim, False, timeout)
        if g is not None:
            verdict = f'COUNTEREXAMPLE deep <= {g}'
        elif done >= law - 1:
            verdict = 'deep = law'
        else:
            verdict = f'deep >= {done + 1}'
        print(al, be, 'n', len(PA), 'j', j, 'law', law, verdict, flush=True)
        os.unlink(path)


if __name__ == '__main__':
    main()
