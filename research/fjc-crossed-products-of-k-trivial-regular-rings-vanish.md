---
rg: 2
id: fjc-crossed-products-of-k-trivial-regular-rings-vanish
kind: claim
title: A crossed product of a K-trivial ring with regular coherent Laurent extensions by a torsion-free Farrell–Jones group is K-trivial
distinct_from:
  leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees: that is one crossed product, L^(⊗d) = C ∗ Z^(d−1), with its own coefficient ring; this is the same assembly argument for every crossed product by every torsion-free group satisfying the conjecture with additive coefficients.
  regular-coherent-laurent-coefficients-kill-twisted-nil-terms: that is the case of the group Z, a skew Laurent ring; this assembles an arbitrary torsion-free Farrell–Jones group from that case and the trivial subgroup.
  crossed-product-rings-inherit-fjc-with-additive-coefficients: that identifies the assembly map and its orbit values for a crossed product; this shows every orbit value vanishes under the ring hypotheses, so the whole target does.
artifacts:
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
---

**ESTABLISHED (derivation from literature imports; unreviewed).** Let `P` be a
torsion-free group that satisfies the `K`-theoretic Farrell–Jones conjecture
with additive categories as coefficients, with respect to `VCyc`. Let `R` be a
unital ring such that:

- `K_n(R) = 0` for every `n ∈ Z` (non-connective algebraic `K`-theory);
- `R[Z^m]` is regular coherent for every `m >= 0`: every finitely presented
  module has a finite resolution by finitely generated projective modules.

Then `K_n(R_(α,τ)P) = 0` for every `n ∈ Z`, for every crossed product
`R_(α,τ)P` in the sense of Bartels–Reich, with `α : P -> Aut(R)`, `α_e = id`,
and `τ : P × P -> R^x` satisfying the cocycle and twisting identities of
`crossed-product-rings-inherit-fjc-with-additive-coefficients`.

**Instances of the hypothesis on `P` in the graph.** Torsion-free virtually
poly-`Z` groups, for example `Z^d`, by
`virtually-poly-z-groups-satisfy-fjc-with-additive-coefficients`.

**Why it matters.** It is the input to
`cantor-crossed-product-leavitt-tensors-are-k-trivial`, which obtains the
`K`-theory condition of `decidable-group-algebras-have-fp-central-simple-hosts`
for hosts that are not coherent.

**Scope.** Torsion-freeness is essential to the argument: for a finite subgroup
the orbit value is a crossed product by a finite group, which is not a Laurent
ring and need not be regular.

No novelty is claimed. It abstracts route
`leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof` from `C ∗ Z^(d−1)` to
any crossed product. Proof: route
`fjc-crossed-products-of-k-trivial-regular-rings-vanish-proof`; details in
Sections 1–3 of the artifact.
