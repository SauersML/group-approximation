"""Bounded Knuth--Bendix test: is r6 (or r7, r8) a consequence of r5 in G0?

Every rule produced is an equality in G0/<<r5>>, so reducing r_i to the empty word proves
r_i in <<r5>>.  Failure to reduce proves nothing (the system is truncated at length MAXLEN).
Alphabet: a, c (involutions), b, B = b^-1.  Shortlex order with a < c < b < B.
"""
import sys, time, itertools
sys.path.insert(0, 'experiments/thompson-v-models')
sys.path.insert(0, 'experiments/thompson-v-relator-blind-2026-09-17')
from census import load, word_str  # noqa: E402

ORD = {'a': 0, 'c': 1, 'b': 2, 'B': 3}
INV = {'a': 'a', 'c': 'c', 'b': 'B', 'B': 'b'}


def inv(w):
    return ''.join(INV[x] for x in reversed(w))


def less(u, v):
    if len(u) != len(v):
        return len(u) < len(v)
    return [ORD[x] for x in u] < [ORD[x] for x in v]


def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == INV[x]:
            out.pop()
        else:
            out.append(x)
    return ''.join(out)


class RS:
    def __init__(self, maxlen):
        self.rules = {}
        self.maxlen = maxlen
        self.lens = set()

    def reduce(self, w):
        changed = True
        while changed:
            changed = False
            for L in sorted(self.lens):
                i = 0
                while i + L <= len(w):
                    s = w[i:i + L]
                    r = self.rules.get(s)
                    if r is not None:
                        w = w[:i] + r + w[i + L:]
                        changed = True
                        i = max(0, i - self.maxlen)
                    else:
                        i += 1
        return w

    def add(self, u, v):
        u, v = self.reduce(u), self.reduce(v)
        if u == v:
            return False
        if less(u, v):
            u, v = v, u
        if len(u) > self.maxlen:
            return False
        self.rules[u] = v
        self.lens.add(len(u))
        return True


def relator_rules(rs, r):
    """All cyclic conjugates of r and r^-1 give equalities u = v^-1 for r = uv."""
    cands = set()
    for w in (r, inv(r)):
        for k in range(len(w)):
            c = w[k:] + w[:k]
            for m in range(len(c) + 1):
                u, v = c[:m], c[m:]
                if len(u) >= len(v):
                    cands.add((u, inv(v)))
    for u, v in cands:
        rs.add(u, v)


def kb(base, maxlen, budget, targets):
    rs = RS(maxlen)
    for x in 'acbB':
        rs.add(x + INV[x], '')
    for r in base:
        relator_rules(rs, r)
    t0 = time.time()
    done = set()
    while time.time() - t0 < budget:
        new = 0
        items = list(rs.rules.items())
        for (l1, r1), (l2, r2) in itertools.product(items, repeat=2):
            if (l1, l2) in done:
                continue
            done.add((l1, l2))
            if rs.rules.get(l1) != r1 or rs.rules.get(l2) != r2:
                continue
            for k in range(1, min(len(l1), len(l2))):
                if l1[-k:] == l2[:k]:
                    w1 = r1 + l2[k:]
                    w2 = l1[:-k] + r2
                    if rs.add(w1, w2):
                        new += 1
            if time.time() - t0 > budget:
                break
        # interreduce
        for l in list(rs.rules):
            r = rs.rules.pop(l)
            rs.lens = {len(x) for x in rs.rules}
            rs.add(l, r)
        res = {name: rs.reduce(w) for name, w in targets.items()}
        print(f'{time.time() - t0:7.0f}s rules={len(rs.rules)} new={new} residues:',
              {k: len(v) for k, v in res.items()}, flush=True)
        if all(v == '' for v in res.values()) or new == 0:
            break
    return rs, res


if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 600
    R = [word_str(w) for w in load('experiments/thompson-v-models/rel_V.txt')]
    base = ['aa', 'cc', 'bbb', 'abababab', 'acacac', R[0]]
    targets = {'r6': R[1], 'r7': R[2], 'r8': R[3]}
    rs, res = kb(base, maxlen, budget, targets)
    for k, v in res.items():
        print(k, 'reduces to', repr(v), 'PROVED in <<r5>>' if v == '' else '(inconclusive)')
