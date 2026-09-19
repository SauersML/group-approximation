# Does the w15 coincidence [u,a] = [v,b] hold for the standard (Brieskorn-path) lifts in P-circ,
# i.e. as 46-strand braids, or only in P?  Also tests each identity used in its derivation.
import sys; sys.path.insert(0, sys.path[0])
from mono import *
name = sys.argv[1] if len(sys.argv) > 1 else 'H4'
A = Arr(name); N = A.N
def br(w):
    b, winv, order = A.braid(w); assert order == A.order0, 'not pure'; return b
def eqP(w1, w2): return same(N, br(w1), br(w2))
P3, P2, P1 = [1, 1], [1, 2, 2, -1], [1, 2, 3, 3, -2, -1]
a = P2 + P3; b = P1 + P3
c = [4, 4]; d = [-3, 4, 4, 3]; w = [2, 3, 4, 4, -3, -2]
u = w + c; v = w + d
tests = {
    '[c,a]=1': (com(c, a), []),
    '[d,b]=1': (com(d, b), []),
    'b = s3^-1 a s3 (as pure loops: b a^-1 = s3^-1 a s3 a^-1)': (b + inv(a), [-3] + a + [3] + inv(a)),
    '[w,b^-1 a]=1': (com(w, inv(b) + a), []),
    '[w,a]=[w,b]': (com(w, a), com(w, b)),
    '[u,a]=[v,b]': (com(u, a), com(v, b)),
}
for k, (x, y) in tests.items():
    print(name, k, ':', eqP(x, y))
# the common value k~ = [u~,a~] is nontrivial and point-pushing (it forgets to the trivial 45-braid)
kk = br(com(u, a))
print(name, 'k~ nontrivial:', not same(N, kk, []), ' k~ point-pushing (in F_45):', same(N - 1, forget(kk, A.order0, N - 1), []),
      ' a~, b~ point-pushing:', all(same(N - 1, forget(br(x), A.order0, N - 1), []) for x in (a, b)))
