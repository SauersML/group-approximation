# Search for q in N, primitive in F_4, with [q] = c_H in H_1(N).
# c_H = 2[F2] + 2[F3] + [F1] as cycles of Gamma_N (support of z split into loops), so every
# product of N-conjugates of F1, F2, F2, F3, F3 (in any order) has class c_H.
import sys, itertools, random
from whitehead import red, inv, is_primitive, minimise, cyc
F1, F2, F3 = 'SpSrs', 'rP', 'QsRq'
BASEN = ['pQ', 'qR', 'rS', F1, F2, F3]
CONJ = [''] + BASEN + [inv(c) for c in BASEN]

def candidates(depth, rng=None, trials=0):
    facs = [F1, F2, F2, F3, F3]
    orders = sorted(set(itertools.permutations(facs)))
    if depth == 0:
        for o in orders: yield ''.join(o)
        return
    for _ in range(trials):
        o = rng.choice(orders)
        w = ''
        for f in o:
            c = ''.join(rng.choice(CONJ) for _ in range(rng.randint(0, depth)))
            w += c + f + inv(c)
        yield red(w)

def check():
    """The loops fix the base point 4 of the index-9 action, and 2F2 + 2F3 + F1 = c_H in H_1(J)."""
    from common import S9, Schreier, U
    a = S9(); sg = Schreier(a, 4)
    for g in BASEN: assert a.img(g, 4) == 4, g
    v = [2 * x + 2 * y + z for x, y, z in zip(sg.ab(F2), sg.ab(F3), sg.ab(F1))]
    assert v == sg.ab(U)
    print('check ok: BASEN fix 4; 2[F2] + 2[F3] + [F1] = c_H in H_1(J)')

if __name__ == '__main__':
    if sys.argv[1] == 'check': check(); sys.exit()
    depth = int(sys.argv[1]); trials = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    rng = random.Random(1)
    best, seen, n = None, set(), 0
    for w in candidates(depth, rng, trials):
        cw = cyc(w)
        if cw in seen: continue
        seen.add(cw); n += 1
        m = minimise(cw)
        if best is None or len(m) < len(best[1]): best = (w, m)
        if len(m) == 1:
            print('PRIMITIVE', w); break
        if n % 500 == 0: print('tested', n, 'best', len(best[1]), flush=True)
    print('tested', n, 'best minimal length', len(best[1]), best)
