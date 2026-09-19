"""Test deep_j(Q) < law_j(Q) in the regime law <= 3 at LARGER n and j.

For a level Q (pullback model pb.py), with seeds one per (type, point):
  L1 = some single lawful seed promotes      (law == 1)
  D1 = some single seed promotes             (deep == 1)
  L2 = some pair of lawful seeds promotes    (law <= 2)
  D2 = some pair of seeds promotes           (deep <= 2)
A FLAG (certified counterexample to (O)) is  D1 and not L1,  or
D2 and not L2.  Pairs are deduplicated by single-seed closure.
Usage: python3 smallk.py mode j n count seed [pairs]
  mode: rand  (random transitive Q)
        exh   (every transitive Q of size n up to isomorphism; count ignored)
"""
import itertools
import random
import sys
import time
from pb import Level, model


def canon(cls):
    first = {}
    return tuple(first.setdefault(c, len(first)) for c in cls)


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


def analyse(PA, PB, j, do_pairs):
    Lv = Level(PA, PB, j, model(j))
    if not Lv.kfib:
        return 'trivial', None
    single = {}
    for (q, ti, law, pr) in Lv.seeds:
        cls = Lv.closure([pr])
        key = canon(cls)
        if key not in single:
            single[key] = [pr, law, Lv.promotes(cls)]
        elif law:
            single[key][1] = True
    L1 = any(v[1] and v[2] for v in single.values())
    D1 = any(v[2] for v in single.values())
    if D1 and not L1:
        return 'FLAG1', [v[0] for v in single.values() if v[2]][0]
    if D1:
        return 'law1', None
    if not do_pairs:
        return 'law>=2 deep>=2', None
    reps = list(single.values())
    L2 = D2 = False
    wit = None
    for x, y in itertools.combinations(reps, 2):
        if L2 and D2:
            break
        both = x[1] and y[1]
        if D2 and not both:
            continue
        cls = Lv.closure([x[0], y[0]])
        if Lv.promotes(cls):
            D2 = True
            if both:
                L2 = True
            elif wit is None:
                wit = (x[0], y[0])
    if D2 and not L2:
        return 'FLAG2', wit
    if L2:
        return 'law2', None
    return 'law>=3 deep>=3', None


def exh_classes(n):
    sys.path.insert(0, '../fpbs-overfold-relative-rank-2026-09-17')
    from exhaustive import cycle_type_reps, canon_form
    classes = set()
    for PA in cycle_type_reps(n):
        for PB in itertools.permutations(range(n)):
            f = canon_form(PA, list(PB))
            if f is not None:
                classes.add(f)
    return [(list(f[:n]), list(f[n:])) for f in sorted(classes)]


def main():
    mode, j, n, count, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), \
        int(sys.argv[4]), int(sys.argv[5])
    do_pairs = len(sys.argv) <= 6 or sys.argv[6] != '0'
    if mode == 'exh':
        levels = exh_classes(n)
    else:
        rng = random.Random(seed)
        levels = []
        while len(levels) < count:
            PA = list(range(n)); rng.shuffle(PA)
            PB = list(range(n)); rng.shuffle(PB)
            if transitive(PA, PB):
                levels.append((PA, PB))
    hist = {}
    t0 = time.time()
    for PA, PB in levels:
        res, wit = analyse(PA, PB, j, do_pairs)
        hist[res] = hist.get(res, 0) + 1
        if res.startswith('FLAG'):
            print(res, 'PA', PA, 'PB', PB, 'witness', wit)
            sys.stdout.flush()
    print('mode', mode, 'j', j, 'n', n, 'levels', len(levels), 'seed', seed,
          'hist', sorted(hist.items()), 'secs %.0f' % (time.time() - t0))


if __name__ == '__main__':
    main()
