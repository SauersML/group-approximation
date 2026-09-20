"""Find threshold pairs whose R_a and R_b are both primitive on the essential alphabet, and print
them in sorted form with the SI-breaking witness word."""
import random
import sys
from treesft import cyc_word, essential, fills, restrict, threshold_pair

n = int(sys.argv[1])
trials = int(sys.argv[2])
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 11)
found = 0
for _ in range(trials):
    w = [rng.gauss(0, 1) for _ in range(n)]
    phi = [rng.gauss(0, rng.choice([.5, 1, 3])) for _ in range(n)]
    psi = [rng.gauss(0, rng.choice([.5, 1, 3])) for _ in range(n)]
    Ra, Rb = threshold_pair(w, phi, psi)
    E = essential(Ra, Rb, n)
    if E == 0:
        continue
    Ra, Rb = restrict(Ra, E, n), restrict(Rb, E, n)
    if fills(E, [Ra], n) and fills(E, [Rb], n):
        found += 1
        if found <= 5:
            syms = [s for s in range(n) if E >> s & 1]
            print("symbols", syms)
            for s in syms:
                print(f"  s={s} w={w[s]:+.2f} phi={phi[s]:+.2f} alpha={phi[s]-w[s]:+.2f} "
                      f"psi={psi[s]:+.2f} beta={psi[s]-w[s]:+.2f} "
                      f"a->{[t for t in syms if Ra[s]>>t&1]} b->{[t for t in syms if Rb[s]>>t&1]}")
            print("  witness", cyc_word(Ra, Rb, n, E))
print("jointly primitive:", found)
