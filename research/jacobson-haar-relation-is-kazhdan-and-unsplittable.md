---
rg: 2
id: jacobson-haar-relation-is-kazhdan-and-unsplittable
kind: claim
title: For n >= 3 the Haar orbit relation of EL_n(J), equivalently the restricted Laurent affine relation, is an ergodic Kazhdan relation, so it is not treeable and is not a nontrivial amalgam over any ergodic subrelation, which kills every halves-gluing route to its soficity
distinct_from:
  jacobson-haar-relation-is-laurent-affine-restriction: that identifies R_E with R_Gamma|_D and reduces soficity of EL_n(J) to it, and remarks only that the group EL_n(A) has (FA); this proves the relation itself is Kazhdan, not treeable, and not a nontrivial amalgam over any ergodic subrelation, which is a relation-level statement the group-level (FA) does not give.
  kazhdan-groupoid-cnd-criterion-and-t-h-exclusion: that imports the general groupoid facts; this applies them to one explicit relation and adds a new general lemma (no nontrivial amalgam of an ergodic Kazhdan relation over an ergodic subrelation).
  kazhdan-relations-coamenable-subrelations-locally-kazhdan: that is about co-amenable Haagerup subrelations; this is about amalgam decompositions and treeings of the whole relation, and it is used here only as a corollary.
  kazhdan-groups-admit-no-treeable-free-action: that is Adams-Spatzier for free actions; the action of EL_n(J) on X_+ is not free, and the non-treeability here comes from AD11 Cor 9.4, which needs no freeness.
  binary-jacobson-el3-is-sofic: that asks whether EL_3(J) is sofic; this does not decide it, but it rules out the treeable and ergodic-amalgam routes to it through the Haar relation.
  atiyah-kazhdan-edge-blocks-both-permanence-routes: that is about a Kazhdan edge group blocking amalgam permanence for Strong Atiyah; here the whole relation is Kazhdan and the amalgam is at the level of measured relations over an ergodic edge subrelation.
artifacts:
  - research/jacobson-haar-relation-kazhdan-proof.md
---

**ESTABLISHED** (route `jacobson-haar-relation-kazhdan-proof`, swarm-0917-w11-w11-nh-follow, 2026-09-18,
unreviewed).

**Setup.** As in `jacobson-haar-relation-is-laurent-affine-restriction`:
* `J = F_2<S,T | TS = 1>` and `E = EL_n(J)`, acting on `(X_+, mu) = ((F_2^n)^N, Haar)`, with orbit relation `R_E`.
* `A = F_2[x, x^(-1)]` and `Γ = A^n x| EL_n(A)`, acting affinely on `F_2((1/x))^n`.
* `D` is the unit ball and `R_Γ|_D` the restricted relation. The w10 theorem gives `R_Γ|_D ≅ R_E`.
* `D_fin = D ∩ A^n` and `R_tail` is the orbit relation of the translations `y -> y + d`, `d in D_fin`, on `D`.
* `Γ_+ = A^n x| EL_n(F_2[x])` and `Γ_- = A^n x| EL_n(F_2[x^(-1)])`, with `R_± = R_(Γ_±)|_D`.

**Amalgams.** Let `R_0 <= R_1, R_2 <= R` be Borel subrelations of a countable p.m.p. relation. Write
`R = R_1 *_(R_0) R_2` if two conditions hold off an `R`-invariant null set:
* `R_1 ∪ R_2` generates `R`;
* (free position, Gaboriau) for every `k >= 1` and every chain `p_0, ..., p_k` with `(p_(i-1), p_i) in R_(j_i) \ R_0`
  and `j_i ≠ j_(i+1)`, we have `(p_0, p_k) ∉ R_0`.

The amalgam is *nontrivial* if `R_1 ≠ R_0` and `R_2 ≠ R_0` on sets of positive measure.

**Theorem.**
1. **(Kazhdan.)** For `n >= 3`, `R_E` is an ergodic p.m.p. relation on a diffuse space with property (T) (Zimmer; AD05
   Def 4.3). Hence so is `R_Γ|_D`.
2. **(Not Haagerup, not treeable.)** `R_E` has neither the Haagerup property nor a treeing. No Haagerup or treeable
   subrelation of it is co-amenable.
3. **(General lemma.)** Let `R` be an ergodic countable p.m.p. relation with property (T). Then `R` is not a nontrivial
   amalgam `R_1 *_(R_0) R_2` over any **ergodic** subrelation `R_0`. No amenability of `R_0` is assumed.
4. **(The halves.)** `R_tail <= R_+ ∩ R_-` and `R_tail` is ergodic. So for `n >= 3`, `R_Γ|_D` is not a nontrivial
   amalgam over any subrelation containing `R_tail`. In particular, `R_Γ|_D = R_+ *_(R_+ ∩ R_-) R_-` can hold only in
   the degenerate case where one half already equals `R_Γ|_D`, so nothing is glued. The same holds for any two
   subrelations that both contain the tail translations.

**What dies (class-kill).** Consider any route to soficity or Connes-embeddability of `EL_n(J)`, `n >= 3` (including
`binary-jacobson-el3-is-sofic`), that passes through the Haar relation and needs one of these inputs:
* (a) a treeing of `R_E` (the Elek--Lippner input: treeable implies sofic);
* (b) a splitting of `R_E` as an amalgam over an ergodic subrelation, for example over hyperfinite `R_tail`, the
  subrelation common to the periodic half `R_+` and the profinite half `R_-` (the input of the amalgam permanence
  theorems over hyperfinite or amenable subrelations);
* (c) a co-amenable Haagerup or treeable subrelation whose approximations ascend.

Every such route dies at the step that produces the input.
* The invariant is relation property (T) of `R_E`, inherited from Kazhdan's property of `EL_n(J)`.
* In (b) the mechanism is the Bass--Serre tree cnd function. It is bounded on a positive piece (AD05 Thm 5.22). The
  ergodic edge relation spreads the bound over the whole space, while nontriviality forces unbounded trees.

**Not covered.**
* Amalgams over non-ergodic `R_0`, and HNN extensions.
* Direct sofic approximation of `R_E`.
* The case `n = 2`, where `EL_2(J)` is not known to be Kazhdan.

Proof: [[jacobson-haar-relation-kazhdan-proof]].
