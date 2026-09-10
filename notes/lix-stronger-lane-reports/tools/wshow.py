import sys
sys.path.insert(0, ".")
from wcoproduct import *

def blocks(M, p):
    return {(i, j): M[i][j] % p for i in range(p) for j in range(p) if M[i][j] % p}

for p in (3, 5):
    psi = build_psi(p, 5)
    print(f"--- p = {p}")
    for n in range(0, 6):
        print(f"  psi(e_{n}):")
        for (a, b), M in sorted(psi[n].items()):
            print(f"     e_{a} (x) e_{b}:  " +
                  ", ".join(f"T^{i}(x)T^{j}:{c}" for (i, j), c in sorted(blocks(M, p).items())))
    print()
# classical candidate check on the even generators
for p in (3, 5, 7):
    psi = build_psi(p, 2 * (p - 1))
    ok_even, ok_oddodd = True, True
    for n in range(0, 2 * (p - 1) + 1):
        for (a, b), M in psi[n].items():
            bl = blocks(M, p)
            if a % 2 == 0 and b % 2 == 0:
                if bl != {(0, 0): 1}:
                    ok_even = False
            if a % 2 == 1 and b % 2 == 1:
                want = {(u, v): 1 for u in range(p) for v in range(p) if u < v}
                if bl != want:
                    ok_oddodd = False
    print(f"p={p}: every (even,even) block is e_a(x)e_b with coefficient 1: {ok_even}; "
          f"every (odd,odd) block is sum_{{u<v}} T^u(x)T^v: {ok_oddodd}")
