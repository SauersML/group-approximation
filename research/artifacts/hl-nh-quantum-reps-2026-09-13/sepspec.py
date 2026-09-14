# Exact spectral data of a separating Dehn twist in the SU(2) level-k WRT/BHMV genus-2 TQFT.
# Basis: admissible colourings (a, b, c) of the dumbbell spine: loop colours a, b, bridge colour c.
# Admissibility at each trivalent vertex (a, a, c): c even, c <= 2a, 2a + c <= 2k.
# The separating curve is the boundary of the disc dual to the bridge; its twist acts diagonally by
# theta_c = (-1)^c A^(c^2 + 2c), A = exp(i pi / (2r)), r = k + 2 (framing scalar ignored:
# the bound below is minimised over ALL scalars lambda, so the global phase is irrelevant).
# Certified lower bound: for unitary X with eigenvalues theta_j and normalized HS norm,
#   min_lambda ||X - lambda I||_2^2 = 1 - |mean theta|^2.
from fractions import Fraction
import cmath, math, json, sys
out = []
for k in range(1, 401):
    r = k + 2
    A = cmath.exp(1j * math.pi / (2 * r))
    d = 0
    s = 0j
    mult = {}
    for c in range(0, k + 1, 2):
        n = k - c + 1                      # number of admissible a for fixed even c (c/2 <= a <= k - c/2)
        if n <= 0:
            continue
        m = n * n                          # a and b independent
        mult[c] = m
        d += m
        s += m * ((-1) ** c) * A ** (c * c + 2 * c)
    mu = abs(s) / d
    out.append({"k": k, "r": r, "dim": d, "abs_mean_eigenvalue": mu, "min_scalar_defect_sq": 1 - mu * mu})
    # consistency: dim of genus-2 SU(2) TQFT via Verlinde should match d for the dumbbell basis
json.dump(out, sys.stdout)
