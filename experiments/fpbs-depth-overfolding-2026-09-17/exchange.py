"""Exchange test: can each overfold seed of a promoting seed set be swapped
for one lawful seed without losing the kernel?

For random Q: build a random seed set P (all types mixed) whose closure
contains ker(Gamma_{j+1} -> Gamma_j), prune it to be minimal, then for each
overfold seed s = (tau, y) in P list the points y' such that
cl(P - s + lawful(y')) still contains ker.  An empty list is an exchange
failure.  Also tracks, per type, which short words w always give a good y'
as y' = y.w (a candidate local exchange rule).
Usage: python3 exchange.py n j trials seed
"""
import random
import sys
from foldlib import random_q, closure, contains_kernel, act
from seedtypes import Seeds


def words(maxlen):
    out = [[]]
    frontier = [[]]
    for _ in range(maxlen):
        nf = []
        for w in frontier:
            for k in [('a', 1), ('a', -1), ('b', 1), ('b', -1)]:
                if w and w[-1][0] == k[0] and w[-1][1] == -k[1]:
                    continue
                nf.append(w + [k])
        out += nf
        frontier = nf
    return out


def sanov_line(p):
    """Q = projective line over F_p, a = [[1,2],[0,1]], b = [[1,0],[2,1]]
    acting on the right on row vectors [x : y]."""
    pts = [(x, 1) for x in range(p)] + [(1, 0)]

    def norm(v):
        x, y = v[0] % p, v[1] % p
        if y:
            return ((x * pow(y, p - 2, p)) % p, 1)
        return (1, 0)
    idx = {q: i for i, q in enumerate(pts)}
    PA = [idx[norm((x, 2 * x + y))] for (x, y) in pts]
    PB = [idx[norm((x + 2 * y, y))] for (x, y) in pts]
    return PA, PB


def main():
    n, j, trials, seed = [int(x) for x in sys.argv[1:5]]
    sanov = len(sys.argv) > 5 and sys.argv[5] == 'sanov'
    n0 = n
    rng = random.Random(seed)
    W = words(4)
    rule = {}
    fails = 0
    tested = 0
    for tr in range(trials):
        PA, PB = sanov_line(n0) if sanov else random_q(n0, rng)
        n = len(PA)
        S = Seeds(PA, PB, j)
        G, m = S.G, S.m
        ok = lambda P: contains_kernel(G, closure(G, [S.seed(t, y) for (t, y) in P]), m)
        allseeds = [(t, y) for t in range(S.ntypes()) for y in range(n)]
        rng.shuffle(allseeds)
        P = []
        for s in allseeds:
            P.append(s)
            if ok(P):
                break
        for s in list(P):
            Q2 = [x for x in P if x != s]
            if ok(Q2):
                P = Q2
        nover = sum(1 for (t, _) in P if t > 0)
        line = ['trial', tr, '|P|', len(P), 'overfold', nover]
        for s in P:
            if s[0] == 0:
                continue
            tested += 1
            rest = [x for x in P if x != s]
            good = [y2 for y2 in range(n) if ok(rest + [(0, y2)])]
            if not good:
                fails += 1
            t, y = s
            gs = set(good)
            okw = {i for i, w in enumerate(W)
                   if act(y, w, PA, PB, S.IA, S.IB) in gs}
            rule[t] = okw if t not in rule else rule[t] & okw
            line += ['|tau%d:%d|' % (t, len(good))]
        print(*line)
        sys.stdout.flush()
    print('overfold seeds tested', tested, 'exchange failures', fails)
    for t in sorted(rule):
        ws = [''.join(l if e == 1 else l.upper() for l, e in W[i])
              for i in sorted(rule[t])][:8]
        print('type', t, 'size', S.sizes[t], 'rep', S.reps[t],
              'always-good words', len(rule[t]), ws)


if __name__ == '__main__':
    main()
