# Audit: complement symmetry and the two-support overlap

Date: 2026-08-30

Claim: `stw82-complement-symmetry-and-overlap-reduction`.

## Checks

1. The common-unitization identity is literal inside `M(A)` and remains
   valid when one of the two algebras is already unital.  Nuclear dimension
   is invariant under minimal unitization, so no extension estimate is
   hidden in the symmetry step.

2. The full-support theorem is applied to `q=1-p` in `M(A)`, not to a
   projection in a different algebra.  Sigma-unitality is retained exactly
   where the existing full-corner argument uses it.

3. `ap,pa in closure(ApA)` follows from the squared-modulus criterion for
   membership in an ideal.  Hence `A=L+R`; the Chinese-remainder quotient by
   `L intersect R` is therefore a direct sum, not merely an injective
   subdirect product.

4. Modulo `L`, the multiplier `p` acts as zero.  Modulo `R`, its complement
   acts as zero, so `p` acts as the multiplier unit.  This gives exactly
   `(A/L) direct_sum (A/R)~` after adjoining `p`.

5. Fullness on the overlap is not inferred from fullness monotonicity.
   It is proved by compressing a finite `LpL` approximation with an
   approximate unit of the ideal `I`; this puts both coefficients in `I`.
   The argument is symmetric for `q`.

6. In the Toeplitz model, `q` is full by an explicit product producing
   `1_T tensor k_1k_2`.  The previously computed nonzero boundary map still
   shows that the one-sided residual extension is nonquasidiagonal, so this
   example genuinely lies beyond the projectional-cut theorem.

## Scope

The theorem does not solve the case where both support ideals are proper
and overlap nontrivially.  It converts that case into an extension whose
quotient already has the correct dimension and whose overlap carries two
full complementary multiplier projections.  Any counterexample must live
in precisely that transition overlap.

Outcome: **PASS**.
