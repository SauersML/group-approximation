"""Run census.py over every admissible type in dimension n, 4 processes.

Usage: python3 driver.py n runs seed
"""
import subprocess
import sys
from itertools import combinations_with_replacement as cwr
from multiprocessing import Pool

n, runs, seed = int(sys.argv[1]), sys.argv[2], sys.argv[3]
As = [c for c in cwr(range(4), n) if sum(c) % 4 == 0 and len(set(c)) > 1]
Bs = [c for c in cwr(range(3), n) if sum(c) % 3 == 0 and len(set(c)) > 1]
jobs = [(''.join(map(str, a)), ''.join(map(str, b))) for a in As for b in Bs]


def run(job):
    out = subprocess.run([sys.executable, 'census.py', str(n), job[0], job[1], runs, seed],
                         capture_output=True, text=True)
    return out.stdout.strip() + out.stderr.strip()[-200:]


if __name__ == '__main__':
    with Pool(4) as p:
        for line in p.imap_unordered(run, jobs):
            print(line, flush=True)
