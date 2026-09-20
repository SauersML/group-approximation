"""Near-centrality of the census minimizers.

For every saved best representation tbest_n*_a*_b*.npz (honest: A^4 = B^3 = (BA)^5 = 1 to 1e-10),
print D_12 = max(||r1 - 1||, ||r2 - 1||), eta = ||[A^2, B]|| (= ||A^2 B A^-2 B^-1 - 1||),
the commutant dimension, and the rotation angles (units of pi) of r1 and r2.

Usage: python3 eta_table.py > eta_table.out
"""
import glob
import numpy as np
import census

print('%-28s %9s %7s %4s  %s' % ('file', 'D_12', 'eta', 'comm', 'r2 angles / pi'))
for f in sorted(glob.glob('tbest_n*.npz'), key=lambda s: (len(s), s)):
    z = np.load(f)
    A, B = z['A'], z['B']
    J = A @ A
    eta = np.linalg.norm(J @ B - B @ J, 2)
    r1, r2, C5 = census.words(A, B)
    assert np.linalg.norm(C5 - np.eye(A.shape[0]), 2) < 1e-10
    D = max(census.opdef(r1), census.opdef(r2))
    ang = np.round(np.sort(np.abs(census.angles(r2))) / np.pi, 4)
    print('%-28s %9.6f %7.4f %4d  %s' % (f, D, eta, census.irreducible(A, B), ang))
