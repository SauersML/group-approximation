import itertools, json
from collections import Counter
from ffold import *
t = sympy.symbols('t')
words = ["".join(tt) for L in (2,3,4) for tt in itertools.product(POS, repeat=L)]
out = []; C = Counter()
for ia, ib, ic in itertools.product(words, repeat=3):
    if len(ia)+len(ib)+len(ic) < 8: continue
    phi = {"a": ia, "b": ib, "c": ic}
    g = gate_of(phi)
    ng = len(set(g.values()))
    if ng < 4: continue
    M = matrix(phi)
    if abs(M.det()) != 1: continue
    if not stallings_is_whole_group([ia, ib, ic]): continue
    if not all(v > 0 for v in M**9): continue
    if not sympy.Poly(M.charpoly(t).as_expr(), t).is_irreducible: continue
    lam = max(abs(complex(r)) for r in sympy.Poly(M.charpoly(t).as_expr(), t).nroots())
    C[ng] += 1
    out.append((ng, lam, phi, str(M.charpoly(t).as_expr()), "".join(g[d] for d in "abcABC")))
print(C)
out.sort(key=lambda o: (-o[0], -o[1]))
for o in out[:25]: print(o)
json.dump(out, open("phi_scan4.json", "w"))
