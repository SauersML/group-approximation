---
rg: 2
id: fpbs-central-amenable-relative-threshold-is-pu-proof
kind: route
title: Enlarge an amenable subgroup by the centre to an amenable wq-normal subgroup and squeeze its relative threshold
target: fpbs-central-amenable-relative-threshold-is-pu
requires:
  - fpbs-amenable-wq-normal-pu-is-relative-pc
  - fpbs-relative-gap-along-any-subgroup-separates
artifacts:
  - research/artifacts/fpbs-f2xz-rigid-relative-gap-2026-09-12.md
---

**1. Monotonicity.** Let `I <= J`. A cluster `K` with `|K ∩ I| = infinity` has
`|K ∩ J| = infinity`. So at every `p` where an `I`-infinite cluster exists a.s.,
a `J`-infinite cluster exists a.s. The set of such parameters for `I` is
contained in the set for `J`, hence `p_c(J;G) <= p_c(I;G)`.

**2. Amenable subgroups.** Let `A` be infinite and amenable, and put `J = AC`.
* **Subgroup.** `C` is central, so `(x,c) -> xc` is a homomorphism
  `A x C -> Gamma`. Its image `J` is a subgroup.
* **Amenable.** `J` is a quotient of `A x C`, which is amenable because `A` is
  amenable and `C` is abelian.
* **Infinite.** It contains `A`.
* **wq-normal, in Popa's sense** as recorded in
  `fpbs-hp-wq-normal-uniqueness-transfer`. Take any intermediate subgroup
  `J <= I' < Gamma` and any `g` outside `I'`. Since `C <= I'` is central,
  `g I' g^(-1) ∩ I' ⊇ gCg^(-1) ∩ C = C`, which is infinite. If `J = Gamma`
  there is no intermediate subgroup, and the condition holds vacuously.

By `fpbs-amenable-wq-normal-pu-is-relative-pc`, `p_c(J;G) = p_u(G)`. Since
`A <= J`, step 1 gives `p_u(G) = p_c(J;G) <= p_c(A;G)`. By
`fpbs-relative-gap-along-any-subgroup-separates`, `p_c(A;G) <= p_u(G)`. Hence
`p_c(A;G) = p_u(G)`.

**3. No weaker premise.** Let `A <= I` with `A` infinite amenable.
* **Implication.** By step 1, `p_c(I;G) <= p_c(A;G)`, and by step 2
  `p_c(A;G) = p_u(G)`. So `p_c(G) < p_c(I;G)` gives `p_c(G) < p_u(G)`.
* **Equivalence when `I` is amenable.** Take `A = I`. Then
  `p_c(I;G) = p_u(G)`, and `p_c(G) < p_c(I;G)` is literally `p_c(G) < p_u(G)`.

No nonamenability of `Gamma`, normality of `A`, or finite generation of `A` is
used.
