# (P_3) for (C2), exactly: F1 = SpSrs, F2 = rP, F3 = QsRq lie in N, and c_H = [F1] + 2[F2] + 2[F3] in H_1(N).
# Here U is the word of the canonical class from the rose node, (T2).  Memberships and the H_1 identity are
# checked after applying phi^k, inside the window T_M (a subgroup of N; phi is an automorphism of N).
from nlib import *
for M in (8, 10):
    g = window(M)
    for k in range(0, 4):
        ws = [pw(u, k) for u in (U, F1, F2, F3)]
        if all(member(g, w) for w in ws):
            lhs = h1(g, ws[0]); rhs = addv((1, h1(g, ws[1])), (2, h1(g, ws[2])), (2, h1(g, ws[3])))
            print('window T_%d, phi^%d: all four in T_M;  [U] = [F1] + 2[F2] + 2[F3] in H_1(T_M):' % (M, k), lhs == rhs)
            break
    else: continue
    break
else: raise SystemExit('not decided in these windows')
# Free factor: pSr, rP, sR together with q form a basis of F_4 (inverse substitution checked in nlib), so
# <pSr, rP, sR> is a free factor, and F1, F2, F3 are conjugates of its basis elements by s, 1, q.
print('basis check: a,b,c,d =', [SPLIT[c] for c in 'abcd'], ' p,q,r,s =', [SPLITI[c] for c in 'pqrs'])
print('F1 = S a s:', red(inv('s') + SPLIT['a'] + 's') == F1, ' F2 = b:', SPLIT['b'] == F2,
      ' F3 = Q c q:', red('Q' + SPLIT['c'] + 'q') == F3)
print('phi in basis B:', PHIB)
