---
rg: 2
id: cubic-division-congruence-sc-forces-asymptotic-laplace-gap-proof
kind: route
title: The heat semigroup of a flat bundle is a norm-convergent group-ring element with compact coefficients, so strong convergence of the monodromy bounds it
target: cubic-division-congruence-sc-forces-asymptotic-laplace-gap
requires: []
---

Write `Gamma = Gamma_D`.

1. **Bundles.**  `Gamma` acts freely, properly and cocompactly by isometries
   on `X`.  Fix a relatively compact Borel fundamental domain `F` whose
   boundary has measure zero.  For a unitary representation `(pi, V)`, the
   `L^2` sections of the flat bundle `X x_Gamma V` are the functions
   `f: X -> V` with `f(gamma x) = pi(gamma) f(x)`.  Restricting to `F` gives
   `L^2(F) (x) V`, and the bundle Laplacian `Delta_pi` is the Laplacian of `X`
   acting on such `f`.  For `pi = l^2(Gamma/Gamma(p))` these sections are the
   functions on `Gamma \ (X x Gamma/Gamma(p)) = Gamma(p) \ X`.  Hence
   `Delta_pi` is the Laplacian of `M_p`: the trivial summand gives the
   pullback of `L^2(M_1)`, and `pi_p` gives its orthogonal complement.
2. **Heat kernel.**  The heat kernel `h_t(x,y)` of `X` is `SL_3(R)`-invariant
   and continuous, with a Gaussian upper bound
   `h_t(x,y) <= C_t exp(-d(x,y)^2 / (8t))`.  (Davies, or Cheng--Li--Yau for
   manifolds with Ricci curvature bounded below; import.  Any bound summable
   against exponential growth suffices.)  Volume growth on `X` is
   exponential, so `#{gamma : d(x, gamma y) <= R} <= C e^(cR)` uniformly for `x, y` in
   the closure of `F`.  Hence `S_t = sum_gamma sup_(x,y in F) h_t(x, gamma y) < infinity`.
3. **Group-ring form.**  Let `a_gamma` be the operator on `L^2(F)` with kernel
   `h_t(x, gamma y)`.  Its kernel is continuous on the compact set
   `closure(F) x closure(F)`, so `a_gamma` is Hilbert--Schmidt, and
   `sum_gamma ||a_gamma|| <= vol(F) S_t`.  For equivariant `f`,
   `(e^(-t Delta) f)(x) = sum_gamma int_F h_t(x, gamma y) pi(gamma) f(y) dy`.  So for every
   unitary `pi`,
   `e^(-t Delta_pi) = K_t(pi) := sum_gamma a_gamma (x) pi(gamma)`,
   and the series converges in norm uniformly in `pi`.  For `pi = lambda_Gamma`,
   `L^2(F) (x) l^2(Gamma) = L^2(X)` and `K_t(lambda) = e^(-t Delta_X)`, whose
   norm is `e^(-t lambda_0(X))`.
4. **Truncation.**  Given `eps > 0`, choose `R` with
   `sum_(|gamma| > R) ||a_gamma|| < eps`.  Then choose a finite-rank projection
   `P` on `L^2(F)` with `sum_(|gamma| <= R) ||a_gamma - P a_gamma P|| < eps`, which is possible
   because each `a_gamma` is compact.  Put
   `x = sum_(|gamma| <= R) P a_gamma P (x) gamma`, an element of `M_n(C[Gamma])` with `n = rank P`.
   Then `||K_t(pi) - (id (x) pi)(x)|| < 2 eps` for every unitary `pi`.
5. **Amplified strong convergence.**  Strong convergence means that for each
   free ultrafilter `omega` the map `C[Gamma] -> prod_omega M_(d_p)` is isometric
   for the reduced norm.  It therefore extends to an injective
   *-homomorphism on `C*_r(Gamma)`.  Injective *-homomorphisms are isometric,
   and so are their `M_n`-amplifications.  Hence
   `lim_p ||(id (x) pi_p)(x)|| = ||(id (x) lambda)(x)||`.
6. **Conclusion.**  `M_p` is compact, so `Delta` on the new part has discrete
   spectrum and no kernel, and `||K_t(pi_p)|| = e^(-t lambda_1^new(p))`.  By steps
   4 and 5, `limsup_p e^(-t lambda_1^new(p)) <= e^(-t lambda_0(X)) + 4 eps` for every
   `eps`.  So `liminf_p lambda_1^new(p) >= lambda_0(X)`.
