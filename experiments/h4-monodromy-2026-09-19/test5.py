# Local lifts at the rank-3 flat L_124 (A_2 x A_1 = the orthogonality A_{s4} _|_ A_{s1 s2} behind w15):
# base point near a generic point of L_124.  Tests [c,a]=1 and the A_2 x A_1 relations as 46-braids.
import sys; sys.path.insert(0, sys.path[0])
from mono import *
name = sys.argv[1] if len(sys.argv) > 1 else 'H4'
for dl in (1e-2, 1e-3):
    A = Arr(name, xc=[dl, 1.3 * dl, 2.3, 1.7 * dl], eps=dl / 7)
    def br(w):
        b, winv, order = A.braid(w); assert order == A.order0; return b
    eq = lambda x, y: same(A.N, br(x), br(y))
    a = [1, 2, 2, -1, 1, 1]; c = [4, 4]
    print(name, 'L_124 d=%g' % dl, '[c,a]=1:', eq(com(c, a), []), ' [s4^2,s1^2]=1:', eq(com(c, [1, 1]), []),
          ' [s4^2,s2^2]=1:', eq(com(c, [2, 2]), []), ' (s1s2)^3=(s2s1)^3:', eq([1, 2] * 3, [2, 1] * 3))
