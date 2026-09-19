"""Check the depth-shift identity numerically:

  seeds of coincidence level >= i at depth j on Q   <->   all seeds at
  depth j-i on the twisted level Q^(i)  (b acting as t_i).

The level of a pair (c, c') of vertices of C_{j+1} is the largest i with
equal images in C_i.  For each random transitive Q we compare
  (number of distinct single-seed closures, number that promote,
   least promoting subset size among pairs <= 2 when it is <= 2)
on both sides.  Equal fingerprints on every Q support the identity
deep_j^{>= i}(Q) = deep_{j-i}(Q^(i)).
Usage: python3 reduction_check.py j i n trials seed
"""
import itertools
import random
import sys
from pb import Level, model, core, iota
from smallk import canon, transitive
sys.path.insert(0, '../fpbs-depth-overfolding-2026-09-17')
from foldlib import t, act, inverse_perm  # noqa: E402


def levels_of_types(j):
    Cs = [core(i) for i in range(j + 2)]
    ios = [iota(Cs[i + 1], Cs[i]) for i in range(j + 1)]
    _, _, _, types = model(j)
    out = []
    for (c, d), law, sz in types:
        x, y, lev = c, d, None
        for i in range(j, -1, -1):
            x, y = ios[i][x], ios[i][y]
            if x == y:
                lev = i
                break
        out.append(lev)
    return out


def fingerprint(Lv, keep):
    single = {}
    for (q, ti, law, pr) in Lv.seeds:
        if not keep(ti):
            continue
        cls = Lv.closure([pr])
        key = canon(cls)
        if key not in single:
            single[key] = (pr, Lv.promotes(cls))
    reps = list(single.values())
    prom1 = sum(1 for r in reps if r[1])
    prom2 = 0
    if prom1 == 0:
        for x, y in itertools.combinations(reps, 2):
            if Lv.promotes(Lv.closure([x[0], y[0]])):
                prom2 += 1
    return (len(reps), prom1, prom2)


def main():
    j, i, n, trials, seed = [int(x) for x in sys.argv[1:6]]
    levs = levels_of_types(j)
    rng = random.Random(seed)
    done = agree = 0
    while done < trials:
        PA = list(range(n)); rng.shuffle(PA)
        PB = list(range(n)); rng.shuffle(PB)
        if not transitive(PA, PB):
            continue
        done += 1
        Lv = Level(PA, PB, j, model(j))
        f1 = fingerprint(Lv, lambda ti: levs[ti] >= i)
        IA, IB = inverse_perm(PA), inverse_perm(PB)
        ti_w = t(i)
        PBt = [act(p, ti_w, PA, PB, IA, IB) for p in range(n)]
        Lt = Level(PA, PBt, j - i, model(j - i))
        f2 = fingerprint(Lt, lambda ti: True)
        agree += f1 == f2
        print('Q', done, 'level>=%d at depth %d' % (i, j), f1,
              '| depth %d on Q^(%d)' % (j - i, i), f2, 'OK' if f1 == f2 else 'MISMATCH')
        sys.stdout.flush()
    print('agree', agree, 'of', trials)


if __name__ == '__main__':
    main()
