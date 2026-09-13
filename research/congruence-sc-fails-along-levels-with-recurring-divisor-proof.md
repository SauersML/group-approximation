---
rg: 2
id: congruence-sc-fails-along-levels-with-recurring-divisor-proof
kind: route
title: A recurring lower level is a fixed finite-dimensional summand, which a nonamenable group cannot weakly contain in its regular representation
target: congruence-sc-fails-along-levels-with-recurring-divisor
requires: []
---

1. **Old levels embed.**  If `M | N` then `Gamma(N) <= Gamma(M)`, so pulling
   functions back along `Gamma/Gamma(N) ->> Gamma/Gamma(M)` is a
   `Gamma`-equivariant isometry (after normalising) sending constants to
   constants.  Hence `sigma := pi_M` is a subrepresentation of `pi_N`, and
   `sigma != 0` because `Gamma(M) != Gamma`.
2. **A nonzero finite-dimensional unitary representation of a nonamenable
   group is not weakly contained in `lambda_Gamma`.**  `sigma (x) conj(sigma)`
   contains the trivial representation (the vector `sum_i e_i (x) conj(e_i)`).
   If `sigma` were weakly contained in `lambda`, then `sigma (x) conj(sigma)`
   would be weakly contained in `lambda (x) conj(sigma)`, which is a multiple
   of `lambda` (Fell absorption).  So `1` would be weakly contained in
   `lambda`, and `Gamma` would be amenable.
3. **A group-ring witness.**  By 2, the kernel of `lambda` in the full group
   C*-algebra is not contained in the kernel of `sigma`, so some `x` has
   `||sigma(x)|| > ||lambda(x)||`.  Let `3 eps = ||sigma(x)|| - ||lambda(x)||`
   and choose `z in C[Gamma]` with `||x - z||_(max) < eps`.  Then
   `||sigma(z)|| > ||lambda(z)|| + eps`.
4. **Conclusion.**  For each of the infinitely many `k` with `M | N_k`,
   step 1 gives `||pi_(N_k)(z)|| >= ||sigma(z)|| > ||lambda(z)|| + eps`.  So
   `limsup_k ||pi_(N_k)(z)|| > ||lambda(z)||`, and the sequence does not
   converge strongly.
