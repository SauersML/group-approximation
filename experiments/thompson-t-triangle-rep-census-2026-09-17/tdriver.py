"""Run tcensus.py over every admissible eigenvalue type in dimension n.

Usage: python3 tdriver.py n batch seed steps procs
"""
import subprocess
import sys
from itertools import combinations_with_replacement as cwr
from multiprocessing import Pool

n, batch, seed, steps, procs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5])
N = int(n)
As = [c for c in cwr(range(4), N) if sum(c) % 4 == 0 and len(set(c)) > 1]
Bs = [c for c in cwr(range(3), N) if sum(c) % 3 == 0 and len(set(c)) > 1]



def cdim(c, n):
    from collections import Counter
    return n * n - sum(m * m for m in Counter(c).values())


# irreducible solutions need dim C_A + dim C_B + dim C_C >= 2(n^2 - 1)
Cs = [c for c in cwr(range(5), N) if sum(c) % 5 == 0]
cmax = max(cdim(c, N) for c in Cs)
jobs = [(''.join(map(str, a)), ''.join(map(str, b))) for a in As for b in Bs
        if cdim(a, N) + cdim(b, N) + cmax >= 2 * (N * N - 1)]
# skip types equivalent under complex conjugation (alpha -> -alpha, beta -> -beta)
seen, uniq = set(), []
for a, b in jobs:
    ca = ''.join(sorted(str((4 - int(x)) % 4) for x in a))
    cb = ''.join(sorted(str((3 - int(x)) % 3) for x in b))
    if (ca, cb) in seen:
        continue
    seen.add((a, b))
    uniq.append((a, b))
jobs = uniq
# most balanced spectra first (largest orbit dimension): these carry the far-from-central irreducibles
jobs.sort(key=lambda j: -(cdim(j[0], N) + cdim(j[1], N)))
print('# n=%s types=%d' % (n, len(jobs)), flush=True)


def run(job):
    out = subprocess.run([sys.executable, 'tcensus.py', n, job[0], job[1], batch, seed, steps],
                         capture_output=True, text=True)
    return out.stdout.strip() + out.stderr.strip()[-300:]


if __name__ == '__main__':
    with Pool(procs) as p:
        for line in p.imap_unordered(run, jobs):
            print(line, flush=True)
