"""Run the directional transvection MITM (mitm_tv) over all primitive directions v with
max |v_i| <= R (one per +-pair), in parallel.  Prints one SUMMARY line per direction and the
first TV line of each direction with collisions, then a TOTAL line.

usage: run_dirs.py BIN k m R [jobs]
"""
import itertools
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from math import gcd


def directions(R):
    out = []
    for v in itertools.product(range(-R, R + 1), repeat=3):
        if not any(v):
            continue
        if gcd(gcd(abs(v[0]), abs(v[1])), abs(v[2])) != 1:
            continue
        first = next(c for c in v if c)
        if first < 0:
            continue
        out.append(v)
    return out


def run(binpath, k, m, v):
    r = subprocess.run([binpath, str(k), str(m)] + [str(c) for c in v], capture_output=True, text=True)
    lines = r.stdout.strip().splitlines()
    tv = [l for l in lines if l.startswith('TV')]
    summ = [l for l in lines if l.startswith('SUMMARY')]
    return v, (tv[0] if tv else None), (summ[0] if summ else 'ERROR ' + r.stderr.strip())


def main():
    binpath, k, m, R = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    jobs = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    dirs = directions(R)
    hitdirs = 0
    with ThreadPoolExecutor(jobs) as ex:
        for v, tv, summ in ex.map(lambda v: run(binpath, k, m, v), dirs):
            print(summ)
            if tv:
                print(tv)
                hitdirs += 1
            sys.stdout.flush()
    print('TOTAL k=%d m=%d R=%d directions=%d directions_with_transvections=%d' % (k, m, R, len(dirs), hitdirs))


if __name__ == '__main__':
    main()
