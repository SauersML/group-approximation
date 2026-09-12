---
rg: 2
id: small-capacity-kk-witness-idempotent-proof
kind: route
title: A gapped witness of capacity below one has finite spectrum, and its spectral projections are algebraic polynomials in it
target: small-capacity-kk-witnesses-are-algebraic-idempotents
requires:
  - integral-spectra-of-small-capacity-are-finite
  - reduced-projection-iff-gapped-spectral-measure
---

Let `a in Z[i][G]` be self-adjoint with `cap(sigma(a)) < 1` and `sigma(a)`
disconnected.

1. By `integral-spectra-of-small-capacity-are-finite` with `n = 1`,
   `sigma(a) = {lambda_1, ..., lambda_r}` is finite, and `m(a) = 0` for the
   squarefree `m = prod_i (x - lambda_i)` in `Z[x]`. Disconnectedness gives
   `r >= 2`.
2. Lagrange interpolation: `e_i = prod_(j != i) (a - lambda_j)/(lambda_i - lambda_j)`
   is a polynomial in `a` with coefficients in `Q(lambda_1, ..., lambda_r)`, so
   it lies in `Qbar[G]`. It equals `chi_({lambda_i})(a)` by functional calculus,
   and `e_i^2 = e_i` in `Qbar[G]` because `m(a) = 0` there. The group ring embeds
   in `C*_r(G)`, so the identity holds algebraically.
3. `tau(e_i) = mu_a({lambda_i})`, strictly between `0` and `1`, because `r >= 2`
   and every atom of `mu_a` has positive mass (`supp mu_a = sigma(a)`, faithful
   trace). So `e_i` is neither `0` nor `1`. Its trace is rational by
   `finite-spectrum-integral-elements-obey-determinant`, applied to the real
   `2 x 2` form of `a` over `Z[G]`.
4. The capacity values quoted in the claim are standard: `cap([s,t]) = (t-s)/4`,
   and `cap(p^(-1)(E)) = cap(E)^(1/d)` for monic `p` of degree `d`, applied with
   `p(x) = x^2` and `E = [a^2, b^2]`.
