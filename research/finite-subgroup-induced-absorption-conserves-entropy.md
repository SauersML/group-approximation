---
rg: 2
id: finite-subgroup-induced-absorption-conserves-entropy
kind: claim
title: Module identities among free and finite-subgroup-induced F_p[G]-modules never change Bernoulli base entropy, over any group
invalidates:
  - leavitt-induced-absorption-gives-bernoulli-collapse
distinct_from:
  lifted-trace-detects-finite-subgroup-projectives: that constructs the additive lifted p-adic trace on K_0(F_p[G]) and evaluates it on finite-subgroup projectives; this reads the same number as the entropy that co-induced Ornstein isomorphisms add, and concludes that the algebraic route to a Bernoulli collapse through induced summands is dead.
  induced-projective-absorption-breaks-bernoulli-classification: that is the implication from an induced absorption to a Bernoulli collapse; this shows its hypothesis never holds.
---

**ESTABLISHED** by [[finite-subgroup-induced-absorption-conserves-entropy-proof]].

Let `G` be a countable group and `p` a prime. For a finite subgroup `F <= G` and a finitely generated
projective `F_p[F]`-module `Q`, put `Ind(Q) = F_p[G] ⊗_(F_p[F]) Q` and `rho(F, Q) = dim(Q)/|F|`. Suppose

    F_p[G]^m ⊕ ⊕_i Ind(Q_i) ≅ F_p[G]^m ⊕ ⊕_j Ind(Q'_j).

Then `sum_i rho(F_i, Q_i) = sum_j rho(F'_j, Q'_j)`. In particular:

1. **No induced absorption.** `F_p[G]^n ≅ F_p[G]^n ⊕ ⊕_i Ind(Q_i)` forces every `Q_i = 0`. So the
   hypothesis of `induced-projective-absorption-breaks-bernoulli-classification` never holds, and
   `leavitt-unit-algebra-absorbs-an-induced-projective` is false.
2. **Entropy is conserved.** Dualizing both sides and applying Corollary D of
   `coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli` gives Bernoulli shifts of base entropies
   `m log p + rho log p` and `m log p + rho' log p`. The theorem says these are equal. The co-induced
   Ornstein construction computes exactly the lifted p-adic trace, times `log p`.

**Reading for the negative direction.**
- An algebraic identity can only produce a Bernoulli collapse through summands whose lifted trace is not
  their entropy. Such summands are not induced from finite subgroups, and their dual actions must be
  shown Bernoulli by other means.
- The absorbed summand `P` of a stable finiteness failure has lifted trace `0`
  (`stable-finiteness-failure-is-algebraic-bernoulli-absorption`). If `X_P` were a Bernoulli shift of
  positive entropy, it would be the first Bernoulli action dual to a projective module whose entropy
  differs from its lifted trace.
- This is the measurable shadow of the finite-subgroup bookkeeping recorded on
  `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units` and
  `leavitt-units-have-laminar-finite-subgroup-defect`: finite-subgroup classes always match the lifted
  trace.
