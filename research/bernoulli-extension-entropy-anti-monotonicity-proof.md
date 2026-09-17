---
rg: 2
id: bernoulli-extension-entropy-anti-monotonicity-proof
kind: route
title: Identify Seward's weakly minimal product with the Bernoulli extension of the orbit relation, and restrict label fields to subrelations
target: bernoulli-extension-entropy-anti-monotone-in-subrelations
requires:
  - seward-weak-containment-relative-entropy-equality
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - amenable-free-actions-weakly-equivalent-to-bernoulli
  - elek-szabo-sofic-permanence
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
artifacts:
  - research/artifacts/orbit-relation-bernoulli-entropy-2026-09-17.md
---

Complete proofs are in Sections 2 to 6 of the artifact.

* **Item 1.** On the preimage of each piece of a Borel partition of `Y`, an element of
  `[R]` agrees with an element of `Γ`, and those pieces lie in `B(Y)`. So
  `σ-alg_Γ(α) ∨ B(Y)` is `[R]`-invariant. Ergodicity of `R̃` comes from a
  mixing-type argument: approximate an invariant set by a cylinder, then move it
  with an aperiodic `T ∈ [R]` until its label support is disjoint off a set of
  measure `n²/M`.
* **Item 2.** `(y, a) ↦ (y, c)` with `c(h y) = a(h^{-1})` is a `G`-equivariant isomorphism
  `Y × L^G → Ỹ` that fixes `B(Y)`. A generator of `L^G` pulled back along the
  projection has the same conditional entropy.
* **Item 3.** Apply Seward Theorem 1.2 with `F` trivial and `X = L^G`.
* **Item 4.** Pull an `S`-generator back along the restriction `c ↦ c|_{[y]_S}`, using
  `Γ_S ⊆ Γ_R`. `Γ_R`-invariance of the generated σ-algebra recovers every label.
* **Item 5.** Chain items 3, 4 and 2.
* **Item 6.** Burton–Kechris and Abért–Weiss (with transitivity) make any free
  action of an amenable group weakly contained in all free actions. Item 3 and
  Seward item 4 then give `H(λ)`, since amenable groups are sofic by Elek–Szabó.
  Restricting `s_G` to an infinite amenable subgroup gives such a subrelation of
  `R_{s_G}`.

Standard facts used inline: Feldman–Moore, transitivity of weak containment,
freeness and mixing of nontrivial Bernoulli shifts, ergodicity of ergodic × mixing,
and existence of an aperiodic element in the full group of an aperiodic relation.
