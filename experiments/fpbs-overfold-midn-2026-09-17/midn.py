"""Mid-n census of the relative form of (O) on random transitive levels.

Usage: python3 midn.py j n count seed smax timeout_s [lawset] [workers]
For each random transitive F(a,b)-set Q of size n (uniform pair of
permutations, rejected unless transitive): export the depth-j instance
(../fpbs-overfold-exact-c-2026-09-17/export.py format), run ./rel with smax,
and print one line: PA PB law and the per-s results.  lawset (comma list)
restricts the expensive search to levels whose law is in it ('-' = all).
Any line containing VIOLATION is an exact certified counterexample to (O).
"""
import os
import random
import re
import subprocess
import sys
import tempfile
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-overfold-exact-c-2026-09-17'))
from export import instance_text  # noqa: E402

REL = os.path.join(HERE, 'rel')


def transitive(PA, PB):
    n = len(PA)
    seen = {0}
    st = [0]
    while st:
        p = st.pop()
        for q in (PA[p], PB[p], PA.index(p), PB.index(p)):
            if q not in seen:
                seen.add(q)
                st.append(q)
    return len(seen) == n


def job(args):
    PA, PB, j, smax, timeout, lawset = args
    text = instance_text(PA, PB, j)
    fd, path = tempfile.mkstemp(suffix='.txt')
    with os.fdopen(fd, 'w') as f:
        f.write(text)
    try:
        out = subprocess.run([REL, path, '0'], capture_output=True, text=True,
                             timeout=timeout).stdout
        m = re.search(r'law (\d+)', out)
        law = int(m.group(1)) if m else None
        if law is None or law <= 1 or (lawset and law not in lawset):
            return f'PA {PA} PB {PB} law {law} skipped'
        try:
            out = subprocess.run([REL, path, str(min(smax, law - 1))],
                                 capture_output=True, text=True,
                                 timeout=timeout).stdout
            tail = ' TIMEOUT' if False else ''
        except subprocess.TimeoutExpired as e:
            out = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or '')
            tail = ' TIMEOUT'
        res = ' | '.join(ln for ln in out.splitlines()
                         if ln.startswith('s ') or ln.startswith('VIOLATION'))
        return f'PA {PA} PB {PB} law {law} :: {res}{tail}'
    except subprocess.TimeoutExpired:
        return f'PA {PA} PB {PB} law-timeout'
    finally:
        os.unlink(path)


def main():
    j, n, count, seed, smax, timeout = map(int, sys.argv[1:7])
    lawset = None
    if len(sys.argv) > 7 and sys.argv[7] != '-':
        lawset = set(int(x) for x in sys.argv[7].split(','))
    workers = int(sys.argv[8]) if len(sys.argv) > 8 else 4
    rng = random.Random(seed)
    levels = []
    while len(levels) < count:
        PA = list(range(n)); rng.shuffle(PA)
        PB = list(range(n)); rng.shuffle(PB)
        if transitive(PA, PB):
            levels.append((PA, PB, j, smax, timeout, lawset))
    print(f'# midn j {j} n {n} count {count} seed {seed} smax {smax} '
          f'timeout {timeout} lawset {sorted(lawset) if lawset else "all"}', flush=True)
    with Pool(workers) as pool:
        for line in pool.imap_unordered(job, levels):
            print(line, flush=True)


if __name__ == '__main__':
    main()
