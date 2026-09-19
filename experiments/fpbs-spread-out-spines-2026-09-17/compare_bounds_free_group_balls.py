"""Compare two lower bounds for p_u^site on Cay(F_2, T_L), T_L = B_L minus e.

Free basis S of F_2, |S| = 4, tree degree q+1 = 4, q = 3.

(1) Spectral (path-counting) bound: p_u^site(Cay(G,T)) >= 1/(|T| rho_T),
    rho_T = norm of the Markov operator of the uniform measure on T.
    For a positive radial f on the (q+1)-regular tree, ||lambda(f)|| equals the
    maximum of |f^(z)| over the Kesten-McKay support [-2 sqrt q, 2 sqrt q],
    where f^(z) = sum_m f(m) chi_m(z) and chi_m is the sphere polynomial
    chi_0 = 1, chi_1 = z, chi_2 = z^2 - (q+1), chi_(m+1) = z chi_m - q chi_(m-1).
    We compute this maximum on a fine grid and compare it with the closed form
    sum_m |S_m| (1 + m (q-1)/(q+1)) q^(-m/2) (Haagerup's ground spherical function).

(2) Cost bound (this node, Corollary C): with eps0 = (C* - 1)/(|S|/2 - 1) = 1,
    p_u^site >= min(eps0/2, sqrt(eps0 / (2 |T| (L-1)))).
"""
import math

q = 3
S_size = 4
Cstar = 2.0
eps0 = (Cstar - 1.0) / (S_size / 2.0 - 1.0)


def sphere_size(m):
    return 1 if m == 0 else (q + 1) * q ** (m - 1)


def sphere_polys(z, L):
    chi = [1.0, z]
    if L >= 2:
        chi.append(z * z - (q + 1))
    for m in range(2, L):
        chi.append(z * chi[m] - q * chi[m - 1])
    return chi[: L + 1]


def rho_T_times_T_numeric(L, grid=20001):
    a = 2.0 * math.sqrt(q)
    best = 0.0
    for i in range(grid):
        z = -a + 2.0 * a * i / (grid - 1)
        chi = sphere_polys(z, L)
        val = abs(sum(chi[m] for m in range(1, L + 1)))
        best = max(best, val)
    return best


def rho_T_times_T_closed(L):
    return sum(
        sphere_size(m) * (1.0 + m * (q - 1.0) / (q + 1.0)) * q ** (-m / 2.0)
        for m in range(1, L + 1)
    )


print("L  |T|        spectral_bound   cost_bound      ratio cost/spectral   (numeric vs closed |T|rho_T)")
for L in range(2, 21):
    T = sum(sphere_size(m) for m in range(1, L + 1))
    num = rho_T_times_T_numeric(L) if L <= 14 else float("nan")
    clo = rho_T_times_T_closed(L)
    spec = 1.0 / clo
    cost = min(eps0 / 2.0, math.sqrt(eps0 / (2.0 * T * (L - 1))))
    print(
        f"{L:2d} {T:10d}  {spec:.6e}   {cost:.6e}   {cost/spec:10.4f}            ({num:.6e} vs {clo:.6e})"
    )
