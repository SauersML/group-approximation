"""Run fcensus.py (random mode) over the near-balanced admissible types of U(n).

Near-balanced: every multiplicity of A (resp. B) is within TOL (default 1.5) of n/4 (resp. n/3).  Admissible:
sum(alpha) = 0 mod 4 and sum(beta) = 0 mod 3 (det(BA) is a 5th root and a 12th root, so 1).
Types equal under complex conjugation are run once.

Usage: python3 fdriver.py n batch seeds steps procs [TOL]
"""
import subprocess
import sys
from itertools import product
from multiprocessing import Pool

n, batch, seeds, steps, procs = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], int(sys.argv[5])
TOL = float(sys.argv[6]) if len(sys.argv) > 6 else 1.5


def near(k):
    for m in product(range(0, n + 1), repeat=k):
        if sum(m) == n and all(abs(x - n / k) <= TOL for x in m):
            yield m


def word(m):
    return ''.join(str(j) * c for j, c in enumerate(m))


As = [word(m) for m in near(4) if sum(j * c for j, c in enumerate(m)) % 4 == 0]
Bs = [word(m) for m in near(3) if sum(j * c for j, c in enumerate(m)) % 3 == 0]
seen, jobs = set(), []
for a in As:
    for b in Bs:
        ca = ''.join(sorted(str((4 - int(x)) % 4) for x in a))
        cb = ''.join(sorted(str((3 - int(x)) % 3) for x in b))
        if (ca, cb) in seen:
            continue
        seen.add((a, b))
        for s in range(seeds):
            jobs.append((a, b, str(1000 * n + s)))
print('# n=%d types=%d jobs=%d' % (n, len(seen), len(jobs)), flush=True)
if len(sys.argv) > 7 and sys.argv[7] == 'dry':
    print(' '.join(a + '/' + b for a, b in sorted(seen)))
    sys.exit(0)


def run(job):
    out = subprocess.run([sys.executable, 'fcensus.py', 'random', str(n), job[0], job[1], batch, job[2], steps],
                         capture_output=True, text=True)
    return out.stdout.strip() + (' seed=' + job[2]) + out.stderr.strip()[-300:]


if __name__ == '__main__':
    with Pool(procs) as p:
        for line in p.imap_unordered(run, jobs):
            print(line, flush=True)
