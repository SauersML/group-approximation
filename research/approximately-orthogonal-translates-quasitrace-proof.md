---
rg: 2
id: approximately-orthogonal-translates-quasitrace-proof
kind: route
title: Compare the row matrix of square roots with its diagonal, using the quarter-power bound on off-diagonal products
target: approximately-orthogonal-unitary-translates-kill-quasitraces
requires: []
artifacts:
  - research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md
---

Full proof: `research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md`
Proposition 4.3. Put `a_i = u_i a u_i*`.

1. **Quarter-power bound.** For positive contractions `b, c`:
   `‖b^{1/2} c^{1/2}‖² = ‖c^{1/2} b c^{1/2}‖`, and
   `‖c^{1/2} b c^{1/2}‖² ≤ ‖b c b‖ ≤ ‖bc‖`.
2. **Row matrix.** Let `X ∈ M_m(A)` have first row `(a_i^{1/2})_i`. Then
   `XX* = (Σ a_i) ⊕ 0` and `X*X = diag(a_i) + E`, with `‖E‖ ≤ m δ^{1/4}`. In
   particular `‖Σ a_i‖ ≤ 1 + m δ^{1/4}`.
3. **Comparison.** Let `σ̃` be the extension of `σ` to `M_m(A)`. It satisfies:
   - `σ̃(diag(a_i)) = m σ(a)`, by commuting additivity and unitary invariance;
   - `σ̃(X*X) = σ̃(XX*) = σ(Σ a_i) ≤ ‖Σ a_i‖ σ(1)`;
   - `|σ̃(X*X) − σ̃(diag(a_i))| ≤ ‖E‖ m σ(1)`, by the unital continuity estimate
     `b − ε 1 ≤ c ≤ b + ε 1` together with monotonicity.
4. **Conclusion.** `m σ(a) ≤ (1 + m δ^{1/4} + m² δ^{1/4}) σ(1)`.
5. **Ideal form.** `σ(a) = 0` iff `a^{1/2} ∈ N_σ`, and each `N_σ` is a closed
   two-sided ideal. So the null positive elements are the positive part of
   `∩_σ N_σ`.

Self-contained derivation from the 2-quasitrace axioms. No literature import.
