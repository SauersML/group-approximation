---
rg: 2
id: surjunctivity-commensurability-invariance-proof
kind: route
title: Read an automaton over a finite-index overgroup as an automaton over the subgroup with a product alphabet
target: surjunctivity-is-a-commensurability-invariant
requires:
  - surjunctivity-passes-to-subgroups
artifacts:
  - research/artifacts/surjunctivity-closure-properties-2026-09-12.md
---

Section 1 of the artifact.

1. For `G = ⊔_i H r_i`, the map `Φ(x)(h) = (x(h r_i))_(i<=n)` is a homeomorphism
   `A^G -> (A^n)^H`. It intertwines the left `H`-shifts, since `Φ(k.x)(h) = Φ(x)(k^-1 h)`.
2. An injective automaton `τ` over `G` commutes with the `H`-shifts. So `Φ τ Φ^-1` is a continuous,
   equivariant, injective self-map of `(A^n)^H`, and by Curtis–Hedlund–Lyndon it is an automaton over `H`.
3. Surjunctivity of `H` makes it onto, and hence `τ` is onto.

For commensurability, compose with heredity to subgroups.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 6.1 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
