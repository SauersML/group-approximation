---
rg: 2
id: fg-infinite-shift-similar-groups-are-strongly-shift-similar
kind: claim
title: Every finitely generated infinite shift-similar group is strongly shift-similar (the finitely generated form of Mallery-Zaremsky Question 3.18); if true, Mallery-Zaremsky Question 5.13 is fully answered
requires:
  - infinite-shift-similar-groups-need-not-be-strongly-shift-similar
  - strongly-shift-similar-type-f-m-passes-to-houghton-like-groups
distinct_from:
  infinite-shift-similar-groups-need-not-be-strongly-shift-similar: that answers Question 3.18 as printed, with a group that is not finitely generated; this is the finitely generated version, which is what Observation 5.12 and Question 5.13 of the source need.
---

**OPEN.** A yes or no answer both count as progress.

**Statement.** If `G <= Sym(N)` is infinite, shift-similar and finitely generated, then `psi_infinity` is onto,
i.e. `G` is strongly shift-similar (Mallery--Zaremsky arXiv:2202.00822v2, Definition 3.17).

**Equivalent germ form.** Let `c` be conjugation by the shift `σ(i) = i+1` on `Sym(N)/FSym(N)`, as in step 1 of
`infinite-shift-similar-groups-need-not-be-strongly-shift-similar`. The statement says: no finitely generated
subgroup `Γ <= Sym(N)/FSym(N)` satisfies `c(Γ) ⊊ Γ`.
- *Why this is equivalent.* An infinite shift-similar `G` contains `FSym(N)` (Theorem 3.12), so it is the preimage
  of `Γ = G/FSym`. It is finitely generated iff `Γ` is, because `FSym(N)` is the normal closure of one
  transposition. Shift-similarity is `c(Γ) ⊆ Γ`, and strong shift-similarity is `c(Γ) = Γ`.
- *Near-action form.* A counterexample `Γ` makes `Δ = < Γ, σ̄ >` a finitely generated subgroup of the near
  symmetric group whose index-zero part `∪_k c^-k(Γ)` is a strictly ascending union. It is therefore not finitely
  generated (compare Corollary 5.6 of the source).
- *A test case.* `c(x) = x^2` with `x` of infinite order would give one, since `c(<x>) = <x^2>`. That is a near
  action of `BS(1,2)` in which `t` acts as the shift. Neither this lane nor the source knows whether one exists.

**Why it matters.**
- If true, every group satisfying the hypotheses of Question 5.13 (finitely presented, or of type `F_m`) is finite
  or strongly shift-similar.
  - Finite shift-similar groups are the `S_m` (Lemma 3.6), with `H_n(G) = H_n` (Observation 5.2), of type
    `F_(n-1)` (Brown).
  - The strongly shift-similar case is `strongly-shift-similar-type-f-m-passes-to-houghton-like-groups`.
  - So all three sentences of Question 5.13 would be answered positively.
- If false, a finitely generated counterexample would test sentences 1–2 of Question 5.13 on a genuinely new
  class. Its `H_1(G)` is not finitely generated (Observation 5.12).

**Attempts.**
- *Sparse transpositions* (the non-finitely-generated example). Adding finitely many generators that shift the
  sparse pattern tends to add the flip-type germs of `E_2`, which make `c` onto again. An example: `x` a sparse
  product of transpositions on even pairs, and `μ` the flip `(1 2)(3 4)...`. Then `c(x) = μ x μ`, and
  `c(< x, Germs(E_2) >) = < x, Germs(E_2) >`.
- *Commensurated subsets for `BS(1,2)`.* The affine action on `Z[1/2]` (`a = +1`, `t = /2`) was tried with subsets
  `{y >= 0 : den(y) <= f(y)}`. None is commensurated by both `a` and `t`: bounded denominators break `t`, and
  unbounded ones break `a` at infinitely many jumps. No counterexample and no proof.
