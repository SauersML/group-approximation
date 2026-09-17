---
rg: 2
id: bernoulli-extension-entropy-anti-monotone-in-subrelations
kind: claim
title: Bernoulli-extension entropy of orbit relations is anti-monotone in subrelations and full on amenable ones, so Rokhlin maximality descends along relation containment but never lifts from subrelations
distinct_from:
  seward-weak-containment-relative-entropy-equality: that is Seward's product equality for a group action; this identifies the product with the Bernoulli extension of the orbit relation, shows the resulting entropy depends only on the relation, and proves anti-monotonicity in subrelations.
  seward-direct-product-relative-rokhlin-entropy-conjecture: that is the open equality for products with arbitrary actions; this uses only the weakly minimal case and moves the statement to orbit relations.
  bernoulli-rokhlin-maximality-passes-to-subgroups: that transfers maximality to subgroups by restricting partitions; this transfers it to any group with a free ergodic action whose orbit relation sits inside a weakly minimal orbit relation, which contains the infinite-subgroup case.
  free-action-containing-nonsofic-group-relation-is-nonsofic: that transfers nonsoficity up along containment of orbit relations; this transfers Bernoulli Rokhlin maximality down along containment of orbit relations.
  rokhlin-permanence-toolkit-certifies-only-sofic-groups: that is the barrier for six group-level permanence operations; this adds a relation-level permanence and records that it also enters no nonsofic group from a sofic seed.
  weak-invariants-give-no-bernoulli-rokhlin-lower-bound: that kills lower bounds from weak equivalence invariants; this kills lower bounds lifted from subrelations, because the invariant is full on every amenable subrelation.
artifacts:
  - research/artifacts/orbit-relation-bernoulli-entropy-2026-09-17.md
---

Let `R` be an ergodic aperiodic p.m.p. countable Borel equivalence relation on
`(Y, ν)` and `(L, λ)` a finite probability space. The **Bernoulli extension**
`R̃` is `Ỹ = {(y, c) : c : [y]_R → L}` with an iid `λ` field on each class, and
`φ ∈ [R]` acts by `(y, c) ↦ (φ y, c)`. Put

`ε_R(L, λ) = inf { H(α | B(Y)) : σ-alg_Γ(α) ∨ B(Y) = B(Ỹ) }`

for a countable group `Γ ⊆ [R]` generating `R`.

1. `ε_R` does not depend on the choice of `Γ`, and `R̃` is ergodic.
2. If `G ↷ (Y, ν)` is free and ergodic with orbit relation `R_Y`, then
   `ε_{R_Y}(L) = h_G(Y × L^G | B(Y)) ≤ h^Rok_G(L^G)`.
3. If in addition `G ↷ Y` is weakly contained in all free p.m.p. actions of `G`
   (e.g. `Y = [0,1]^G`), then `h^Rok_G(L^G, λ^G) = ε_{R_Y}(L, λ)`.
4. **Anti-monotone.** If `S ⊆ R` are both ergodic aperiodic on `(Y, ν)`, then
   `ε_R ≤ ε_S`.
5. **Relation permanence.** Let `G ↷ Y` be as in 3, and let `H ↷ (Y, ν)` be a free
   ergodic action of a countably infinite group whose orbit relation lies in `R_Y`.
   Then `h^Rok_G(L^G) ≤ h^Rok_H(L^H)`. So Rokhlin-maximality passes from `G` to `H`,
   and two groups with orbit-equivalent weakly minimal free actions have equal
   Bernoulli Rokhlin entropies.
6. **Obstruction.** If `S` is the orbit relation of a free ergodic action of a
   countably infinite amenable group, then `ε_S(L, λ) = H(L, λ)`. By 4, lower bounds
   on `ε` pass only from a relation to its subrelations. Any principle that lifts
   fullness of `ε` from a subrelation to an ambient relation would, with 3, prove
   Rokhlin-maximality for every group containing an infinite amenable subgroup.
   It is as strong as the flagship INF statement, not a reduction of it.

**ESTABLISHED 2026-09-17** by
[[bernoulli-extension-entropy-anti-monotonicity-proof]].

Coordination note: `a-gs-tester-host` is independently drafting the orbit-relation
invariance of relative Bernoulli entropy over a free base, with OE transfer of
`h_sup`, under the id `bernoulli-rokhlin-entropy-is-an-orbit-relation-invariant`.
Items 1 to 3 here overlap with that draft and are proved self-contained in the
artifact. The new content of this node is items 4 to 6.
