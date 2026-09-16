#!/usr/bin/env python3
"""Wider partial-positivity search on the length-16 classes left open by primcert.py.

census3.py searched automorphic images of length <= |w| + 4 (cap 20000).  The orbits of these
Whitehead-minimal relators are small, so the bound can be raised.  Breadth-first search over the
Whitehead moves census.WH (cyclic words up to rotation), length <= |w| + EXTRA, stopping at the first
partially positive image (some generator occurs with one sign only).  Every hit is re-derived by
replaying the recorded move sequence from w.
Usage: ppwide.py PRIMCERT_OUT EXTRA CAP
"""
import sys, os
from collections import deque
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'research/artifacts/or-unpeelable-census-scripts-2026-09-12'))
import census as C
import census2 as C2


def search(w, extra, cap):
    w = C.cyc_reduce(w)
    bound = len(w) + extra
    parent = {C2.ckey(w): None}
    dq = deque([w])
    while dq:
        v = dq.popleft()
        if C.pp(v):
            path, k = [], C2.ckey(v)
            while parent[k] is not None:
                k, i = parent[k]
                path.append(i)
            return v, path[::-1], len(parent)
        kv = C2.ckey(v)
        for i, img in enumerate(C.WH):
            u = C.cyc_reduce(C.subst(v, img))
            if len(u) <= bound:
                k = C2.ckey(u)
                if k not in parent:
                    if len(parent) >= cap:
                        return None, 'CAP', len(parent)
                    parent[k] = (kv, i)
                    dq.append(u)
    return None, 'EXHAUSTED', len(parent)


def main():
    extra, cap = int(sys.argv[2]), int(sys.argv[3])
    code = {'a': 1, 'A': -1, 't': 2, 'T': -2}
    todo = []
    for line in open(sys.argv[1]):
        f = line.split()
        if f and f[0] == 'NONPRIM':
            todo.append(f[1])
        elif f and f[0] == 'VERDICT' and not line.rstrip().endswith('-> PASS'):
            todo.append(f[2])
    counts = {}
    for wtxt in todo:
        w = [code[ch] for ch in wtxt]
        v, info, n = search(w, extra, cap)
        if v is None:
            print('NOPP %s %s nodes=%d' % (wtxt, info, n), flush=True)
            counts['NOPP_' + info] = counts.get('NOPP_' + info, 0) + 1
            continue
        u = C.cyc_reduce(w)
        for i in info:
            u = C.cyc_reduce(C.subst(u, C.WH[i]))
        assert C2.ckey(u) == C2.ckey(v) and C.pp(u)
        print('PP %s image=%s len=%d moves=%s nodes=%d' % (wtxt, C.word_str(v), len(v), info, n), flush=True)
        counts['PP'] = counts.get('PP', 0) + 1
    print('COUNTS %s' % sorted(counts.items()))
    print('SENTINEL_DONE', flush=True)


if __name__ == '__main__':
    main()
