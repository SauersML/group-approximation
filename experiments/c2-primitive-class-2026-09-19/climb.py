# Hill-climb in the coset q0 [N,N] for an F_4-primitive element (score = Whitehead-minimal length).
# Moves q -> q [a,b] with a, b short products of the N-elements BASEN; they keep [q] = c_H.
# Usage: python3 climb.py <restarts> <steps> <seed>
import sys, random
from whitehead import red, inv, minimise, cyc
from search import F1, F2, F3, BASEN

GENS = BASEN + [inv(g) for g in BASEN]
START = red(F2 + F2 + F3 + F3 + F1)

def nword(rng, k):
    return red(''.join(rng.choice(GENS) for _ in range(k)))

def climb(rng, steps, cap=160):
    q = START; sc = len(minimise(q)); best = (sc, q)
    for _ in range(steps):
        a, b = nword(rng, rng.randint(1, 3)), nword(rng, rng.randint(1, 3))
        if rng.random() < 0.3: b = q if rng.random() < 0.5 else inv(q)
        cand = red(q + a + b + inv(a) + inv(b))
        if not cand or len(cand) > cap: continue
        s = len(minimise(cand))
        if s <= sc:
            q, sc = cand, s
            if s < best[0]: best = (s, q)
            if s == 1: break
    return best

if __name__ == '__main__':
    R, T, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed); glob = None
    for r in range(R):
        b = climb(rng, T)
        if glob is None or b[0] < glob[0]: glob = b
        print('restart', r, 'best', b[0], flush=True)
        if b[0] == 1: print('PRIMITIVE', b[1]); break
    print('overall best', glob[0], glob[1])
