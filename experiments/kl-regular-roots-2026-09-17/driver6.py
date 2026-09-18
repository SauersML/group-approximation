from euclid import *
w = parse('2 T 5 t 5 T 1')
c = C(1)
cp = mul(mul(((1, 0), 0), c), ((-1, 0), 0))   # rotation by omega about 1
assert mul(mul(c, cp), c) == mul(mul(cp, c), cp), 'braid relation'
tau = mul(mul(C(3), inv(cp)), C(-1))
print('w(tau) =', evalword(w, tau))
D = fox(w, tau)
print('D =', D)
M = right_matrix(D)
d = det_laurent(M)
print('det =', d)
