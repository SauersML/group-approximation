---
rg: 2
id: separated-finite-normal-subgroups-preserve-surjunctivity
kind: claim
title: A finite normal subgroup injecting into a finite quotient does not affect surjunctivity
distinct_from:
  surjunctivity-is-a-commensurability-invariant: that is invariance across finite-index subgroups; this transfers surjunctivity in both directions across the quotient by a finite normal subgroup that some finite-index subgroup avoids, by combining that invariance with heredity.
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

Let `N` be a finite normal subgroup of `E`, and suppose some finite-index subgroup `E_0` meets `N`
trivially; equivalently, `N` injects into a finite quotient of `E`. Then `E` is surjunctive iff `E/N` is.

**Proof idea.** `E_0` maps isomorphically onto the finite-index subgroup `E_0N/N` of `E/N`. Heredity and
commensurability invariance carry surjunctivity across `E ⊇ E_0 ≅ E_0N/N ⊆ E/N` in both directions.
The proof is Section 4 of the artifact.

**Corollary.** Virtually split finite central extensions of surjunctive groups are surjunctive. More
generally, if the center of a finite central extension injects into a finite quotient, the extension is
surjunctive exactly when its quotient is.

**Not covered.** Finite normal subgroups inside the finite residual, for example the center of Deligne's
triple cover of `Sp_4(Z)` (`deligne-triple-cover-finite-residual-is-center`). See
`finite-normal-subgroups-do-not-affect-surjunctivity`.
