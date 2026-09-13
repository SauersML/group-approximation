---
rg: 2
id: cubic-division-congruence-sc-forces-asymptotic-laplace-gap-proof
kind: route
title: Convolution on a flat bundle over a compact quotient is a finite group-ring sum with Hilbert-Schmidt coefficients, so strong convergence of the monodromy bounds it
target: cubic-division-congruence-sc-forces-asymptotic-laplace-gap
requires: []
---

Write `Gamma = Gamma_D`, `G = SL_3(R)`.

1. **Bundles.**  `Gamma` is a cocompact lattice, and it is torsion-free.  A
   torsion element `zeta` of order `n` generates a subfield `Q(zeta) <= D`.
   Its degree `phi(n)` divides 3 and is even for `n >= 3`, so `zeta = +-1`, and
   `Nrd(-1) = -1`.  So `M_p` is a manifold; parts 1 and 2 would not need this.
   Fix a
   relatively compact Borel fundamental domain `F` for the left
   `Gamma`-action on `G`.  For a unitary representation `(pi, V)`, let
   `W_pi` be the space of `phi: G -> V` with `phi(gamma x) = pi(gamma) phi(x)` and
   `int_F |phi|^2 < infinity`.  Restriction to `F` identifies `W_pi` with
   `L^2(F) (x) V`, and `G` acts by right translation.
   - For `pi = l^2(Gamma/Gamma(p))`, `W_pi = L^2(Gamma(p) \ G)`.  The trivial
     summand gives `L^2(Gamma \ G)`, so `pi_p` gives the new part and `R_p` is
     right translation on `W_(pi_p)`.
   - For `pi = lambda_Gamma`, `W_pi = L^2(G)` with the right-regular
     representation, which is equivalent to `lambda_G`.
2. **Group-ring form.**  Let `f in C_c(G)`.  For `phi in W_pi` and `x in F`,
   `(R(f) phi)(x) = int_G f(x^-1 y) phi(y) dy = sum_gamma int_F f(x^-1 gamma y) pi(gamma) phi(y) dy`.
   Let `a_gamma` be the operator on `L^2(F)` with kernel `f(x^-1 gamma y)`.  It is
   nonzero only for `gamma` in `closure(F) supp(f) closure(F)^-1`, a finite set
   `E_f`.  Its kernel is continuous on the compact set
   `closure(F) x closure(F)`, so `a_gamma` is Hilbert--Schmidt.  So for every
   unitary `pi`, `R_pi(f) = sum_(gamma in E_f) a_gamma (x) pi(gamma)`.
3. **Truncation.**  Given `eps > 0`, choose a finite-rank projection `P` on
   `L^2(F)` with `sum_(gamma in E_f) ||a_gamma - P a_gamma P|| < eps`.  Then
   `x = sum_(gamma in E_f) P a_gamma P (x) gamma` lies in `M_n(C[Gamma])`, `n = rank P`, and
   `||R_pi(f) - (id (x) pi)(x)|| < eps` for every unitary `pi`.
4. **Amplified strong convergence.**  Strong convergence says that for each
   free ultrafilter `omega` the map `C[Gamma] -> prod_omega M_(d_p)` is isometric
   for the reduced norm.  So it extends to an injective *-homomorphism on
   `C*_r(Gamma)`, and its `M_n`-amplification is isometric.  Hence
   `lim_p ||(id (x) pi_p)(x)|| = ||(id (x) lambda)(x)||`, and so
   `limsup_p ||R_p(f)|| <= ||lambda_G(f)|| + 2 eps` for every `eps`.  This is part 1.
5. **Part 2.**  If `sigma` is not tempered, some `f_sigma in C_c(G)` has
   `||sigma(f_sigma)|| > ||lambda_G(f_sigma)|| + delta_sigma` with `delta_sigma > 0`: weak
   containment in `lambda_G` is tested on the dense subalgebra `C_c(G)` of
   `C*(G)`.  The set `{sigma' : ||sigma'(f_sigma)|| > ||lambda_G(f_sigma)|| + delta_sigma/2}` is
   open in the Fell topology, since `sigma' -> ||sigma'(f)||` is lower
   semicontinuous.  Cover `C` by finitely many such sets.  If infinitely
   many primes `p` had a constituent `sigma_p` of `R_p` in `C`, infinitely many
   would lie in one set.  Then `||R_p(f_sigma)|| >= ||sigma_p(f_sigma)|| > ||lambda_G(f_sigma)|| + delta_sigma/2`
   infinitely often, contradicting part 1.
6. **Part 3.**  The new part has no `G`-invariant vectors (those are
   constants), so it contains no trivial constituent.  A new Laplace
   eigenvalue `mu` on `M_p` comes from a spherical constituent `sigma_nu` of
   `R_p`.  By Harish-Chandra's spherical theory
   `mu = ||rho||^2 + ||Im nu||^2 - ||Re nu||^2`, and `lambda_0(X) = ||rho||^2`.  So `mu <= lambda_0(X) - eps` forces
   `||Re nu||^2 >= eps` with `nu` bounded, `||Re nu|| <= ||rho||` by unitarity.
   Such unitary spherical representations form a compact set of non-tempered
   representations: tempered spherical means `Re nu = 0`.  Part 2 applies.
   (Standard spherical representation theory; import.  An alternative route
   with the heat kernel and a Gaussian bound gives part 3 directly.)
