"""Certificate for the explicit type A_4 VC failure, through the faithful Artin representation B_5 -> Aut(F_5).
Letters (sigma_i = Artin generators of B_5):  p0 = s1^2, p1 = s1 s2^2 s1^-1, p2 = s1 s2 s3^2 s2^-1 s1^-1  (in F)
                                               x0 = s4^2, x1 = s3 s4^2 s3^-1, x2 = s2 s3 s4^2 s3^-1 s2^-1  (in N)
a = p1 p0, b = p2 p0, w = x2, c = x0, d = x0 x1 x0^-1, u = w c, v = w d.
Checks: c in C(a) \\ C(b); d in C(b) \\ C(a); [w,a] = [w,b] =: k != 1; [u,a] = [v,b] = k; [u,b] != k; [v,a] != k;
and for the Case 1 tuple a1 = a^-1, a2 = b, b3 = u, b1 = u^-1 v: (*) b3^-1 a1 a2 b3 = a1 b1 a2 b1^-1, a1 a2 != 1,
and the three vertex conditions of (V') fail: k = 1, [u,b] = k, [v,a] = k are all false."""
import sys
sys.argv = [sys.argv[0], 'A4', '/dev/null']
exec(open('artinverify.py').read().split('ID = rep([])')[0])
S = {'p0': [1, 1], 'p1': [1, 2, 2, -1], 'p2': [1, 2, 3, 3, -2, -1],
     'x0': [4, 4], 'x1': [3, 4, 4, -3], 'x2': [2, 3, 4, 4, -3, -2]}
assert all(L[k] == v for k, v in S.items()), 'letters differ from dumpgen'
a, b = w('p1 p0'), w('p2 p0'); w_, c, d = w('x2'), w('x0'), w("x0 x1 x0'")
u, v = w_ + c, w_ + d
E = lambda x, y: rep(x) == rep(y); ID = rep([])
k = rep(comm(w_, a))
checks = {
  'c in C(a)': E(c + a, a + c), 'c not in C(b)': not E(c + b, b + c),
  'd in C(b)': E(d + b, b + d), 'd not in C(a)': not E(d + a, a + d),
  '[w,a] = [w,b]': k == rep(comm(w_, b)), 'k != 1': k != ID,
  '[u,a] = k': rep(comm(u, a)) == k, '[v,b] = k': rep(comm(v, b)) == k,
  '[u,b] != k': rep(comm(u, b)) != k, '[v,a] != k': rep(comm(v, a)) != k}
a1, a2, b3, b1 = inv(a), b, u, inv(u) + v
checks['(*)'] = E(inv(b3) + a1 + a2 + b3, a1 + b1 + a2 + inv(b1))
checks['a1 a2 != 1'] = rep(a1 + a2) != ID
for key, val in checks.items(): print(f'{key:16s} {val}')
print('ALL OK' if all(checks.values()) else 'FAILED')
