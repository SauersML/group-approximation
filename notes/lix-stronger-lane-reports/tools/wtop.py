"""The reduced coproduct coefficient at the TOP corner, for higher n."""
import sys
sys.path.insert(0, ".")
from wcoproduct import build_psi, cbar

for p in (3, 5, 7):
    for (q, qq) in [(1, 1), (2, 2), (2, 4), (4, 4), (2, 6)]:
        n = (q + qq) * (p - 1)
        if n > 8 * (p - 1) or (p == 7 and n > 6 * 6):
            continue
        psi = build_psi(p, n)
        cb = cbar(psi, n, p)
        a, b = q * (p - 1), qq * (p - 1)
        v = cb.get((a, b), 0) % p
        odd_ok = all(x % p == 0 for (aa, bb), x in cb.items() if aa % 2 == 1)
        even_ok = all(x % p == 1 for (aa, bb), x in cb.items() if aa % 2 == 0)
        print(f"p={p} (q,q')=({q},{qq})  n={n}:  cbar_({a},{b}) = {v}   "
              f"[a odd -> 0: {odd_ok}; a even -> 1: {even_ok}]", flush=True)
