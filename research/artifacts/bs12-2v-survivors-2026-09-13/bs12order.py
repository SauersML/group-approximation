#!/usr/bin/env python3
"""Exact classification of SURVIVOR tables printed by bs12survive.py.

Each table is reduced after every composition (sibling brick pairs split on the
same coordinate with matching last digits are merged). For p = 1..KMAX:
  ORDER p    g^p = id (exact finite order p, first such p);
  HYP p      g^p has a fixed point with nonzero exponent (excluded for every
             conjugator by item 2 of the open-periodic-sets claim);
  BLOWUP p   reduced table of g^p exceeds CAP bricks (undecided);
  OPEN       none of the above up to KMAX.
Usage:  bs12order.py selftest | bs12order.py FILE [KMAX]
"""
import sys, ast, hashlib
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from bs12search import compose, is_identity
from bs12survive import hyperbolic_fixed_brick

CAP = 20000

def reduce_table(g):
    pairs = set(g)
    changed = True
    while changed:
        changed = False
        for d, r in list(pairs):
            if (d, r) not in pairs:
                continue
            for j in range(len(d)):
                if d[j].endswith('0') and r[j].endswith('0'):
                    d1 = tuple(x[:-1] + '1' if i == j else x for i, x in enumerate(d))
                    r1 = tuple(x[:-1] + '1' if i == j else x for i, x in enumerate(r))
                    if (d1, r1) in pairs:
                        pairs.discard((d, r)); pairs.discard((d1, r1))
                        pairs.add((tuple(x[:-1] if i == j else x for i, x in enumerate(d)),
                                   tuple(x[:-1] if i == j else x for i, x in enumerate(r))))
                        changed = True
                        break
    return tuple(sorted(pairs))

def classify(g, kmax):
    g = reduce_table(g)
    p = g
    for k in range(1, kmax + 1):
        if is_identity(p):
            return 'ORDER', k
        if hyperbolic_fixed_brick(p) is not None:
            return 'HYP', k
        if len(p) > CAP:
            return 'BLOWUP', k
        p = reduce_table(compose(g, p))
    return 'OPEN', kmax

def selftest():
    ws = [format(i, '06b') for i in range(64)]
    c64 = tuple(((ws[i], ''), (ws[(i + 1) % 64], '')) for i in range(64))
    assert classify(c64, 200) == ('ORDER', 64), classify(c64, 200)
    split = ((('0', ''), ('0', '')), (('1', ''), ('1', '')))
    assert reduce_table(split) == ((('', ''), ('', '')),), reduce_table(split)
    b = ((('0', ''), ('', '0')), (('1', ''), ('', '1')))
    assert classify(b, 10) == ('HYP', 1)
    print('selftest OK')

def main(path, kmax):
    seen, counts = set(), {}
    for line in open(path):
        if not line.startswith('SURVIVOR'):
            continue
        table = ast.literal_eval(line.split(' ', 2)[2].rsplit(' [', 1)[0])
        key = reduce_table(table)
        if key in seen:
            counts['duplicate'] = counts.get('duplicate', 0) + 1
            continue
        seen.add(key)
        cls, k = classify(table, kmax)
        counts[cls] = counts.get(cls, 0) + 1
        if cls != 'ORDER':
            print(cls, k, key, flush=True)
        else:
            counts['order%d' % k] = counts.get('order%d' % k, 0) + 1
    print('SUMMARY', path, 'KMAX=%d' % kmax, ' '.join(
        '%s=%d' % kv for kv in sorted(counts.items())), flush=True)

if __name__ == '__main__':
    print('md5 bs12order.py', hashlib.md5(open(__file__, 'rb').read()).hexdigest(), flush=True)
    if sys.argv[1] == 'selftest':
        selftest()
    else:
        main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 4096)
