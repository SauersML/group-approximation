import sys
sys.path.insert(0, ".")
from steenrod_descent import *

for p in (3, 5):
    C = RelSimplexCochains(2)
    u0 = (1, 2)
    du = C.delta[u0]
    print("p =", p, " delta g =", du)
    (top, ct), = du.items()
    A = {(top,) * p: ct % p}
    W = 2 * (p - 1)
    while W > 0:
        show = {"".join(str(C.deg[l]) for l in w): (c if c <= p // 2 else c - p)
                for w, c in sorted(A.items())}
        print("  W-index", W, "|A| =", len(A), (show if len(A) < 14 else "..."))
        Y = Hop(C, A, p)
        chk = Dop(C, Y, p)
        print("     |Y| =", len(Y), " D(Y) == A ?", not addv(chk, A, p, -1),
              " D(A) == 0 ?", not Dop(C, A, p))
        op, nm = (Nop, "N") if W % 2 == 0 else (TminusOne, "(T-1)")
        A = op(C, Y, p)
        W -= 1
    print("  final |A| =", len(A), "c_2 =", pair_with_aw(C, A, 2, p))
    print()
