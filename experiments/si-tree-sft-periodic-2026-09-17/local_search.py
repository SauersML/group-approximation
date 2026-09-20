"""Hill-climb over threshold parameters (w, phi, psi) to minimise the SI defect of the
threshold pair (a pair with no periodic point). Defect 0 would be an SI F_2-SFT without
periodic points. Symbols dropped by the essential restriction are penalised."""
import random
import sys
from treesft import essential, si_defect, threshold_pair, periodic, restrict, show

n = int(sys.argv[1])
iters = int(sys.argv[2])
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
restarts = int(sys.argv[4]) if len(sys.argv) > 4 else 20
rng = random.Random(seed)


def score(p):
    w, phi, psi = p
    Ra, Rb = threshold_pair(w, phi, psi)
    E = essential(Ra, Rb, n)
    k = bin(E).count("1")
    if k == 0:
        return 10 ** 9, None
    bad, tot = si_defect(Ra, Rb, n, E)
    return bad + 50 * (n - k), (Ra, Rb, E)


overall = None
for r in range(restarts):
    p = [[rng.gauss(0, 1) for _ in range(n)] for _ in range(3)]
    sc, info = score(p)
    T = 2.0
    for it in range(iters):
        q = [row[:] for row in p]
        i = rng.randrange(3)
        j = rng.randrange(n)
        q[i][j] += rng.gauss(0, 0.5)
        sq, iq = score(q)
        if sq <= sc or rng.random() < pow(2.718, (sc - sq) / T):
            p, sc, info = q, sq, iq
        T = max(0.05, T * 0.999)
        if sc == 0:
            break
    print(f"restart {r}: final score {sc}")
    if overall is None or sc < overall[0]:
        overall = (sc, p, info)
    if sc == 0:
        Ra, Rb, E = info
        print("SI WITHOUT PERIODIC POINT", p)
        print(show(Ra, n), "|", show(Rb, n), bin(E))
        print("LP periodic:", periodic(restrict(Ra, E, n), restrict(Rb, E, n), n))
        break
print("best", overall[0])
if overall[2] is not None:
    from treesft import cyc_word
    sc, p, (Ra, Rb, E) = overall
    w, phi, psi = p
    order = sorted(range(n), key=lambda s: w[s])
    for s in order:
        print(f"  s={s} w={w[s]:+.2f} phi={phi[s]:+.2f} alpha={phi[s]-w[s]:+.2f} "
              f"psi={psi[s]:+.2f} beta={psi[s]-w[s]:+.2f} "
              f"a->{[t for t in range(n) if Ra[s]>>t&1]} b->{[t for t in range(n) if Rb[s]>>t&1]}")
    print("  witness", cyc_word(Ra, Rb, n, E))
