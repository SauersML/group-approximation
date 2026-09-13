---
rg: 2
id: fp-n-splittings-over-fp-n-edges-have-fp-n-vertex-groups-proof
kind: route
title: "Bass--Serre chains, induced modules and the Bieri--Eckmann criterion force FP_n vertex groups"
target: fp-n-splittings-over-fp-n-edges-have-fp-n-vertex-groups
requires: []
---

Tools: the Bieri--Eckmann criterion (R. Bieri, *Homological dimension of
discrete groups*, Queen Mary College Notes, 2nd ed. 1981, Chapter 1; K. S.
Brown, *Cohomology of groups*, Section VIII.4). A left module `A` over a ring
`R` is of type `FP_n` iff for every family of copies of `R` the natural map
`c_k: Tor_k^R(∏ R, A) -> ∏ Tor_k^R(R, A)` is an isomorphism for `k < n` and an
epimorphism for `k = n`.

**Step 1: `Ind_K^H Z` is of type `FP_n` over `ZH` iff `K` is of type `FP_n`.**
If `K` is of type `FP_n`, induce a partial resolution of `Z` by finitely
generated free `ZK`-modules. `ZH` is free as a right `ZK`-module, so exactness
is kept and finitely generated free modules stay finitely generated free.
Conversely, for a right `ZH`-module `X` there is a natural isomorphism
`Tor_k^{ZH}(X, ZH ⊗_{ZK} Z) ≅ Tor_k^{ZK}(X, Z)` (`ZH` is flat over `ZK`). As
right `ZK`-modules, `ZH = ZK ⊕ C` with `C` the sum over the nontrivial cosets,
so `∏ ZH = ∏ ZK ⊕ ∏ C`. The criterion map for `K` (with `∏ ZK`) is therefore a
direct summand of the criterion map for `Ind_K^H Z` (with `∏ ZH`), naturally in
the family. A direct summand of an isomorphism is an isomorphism, and a direct
summand of an epimorphism is an epimorphism, so `K` is of type `FP_n`.

**Step 2: extensions and summands.** If `0 -> M' -> M -> M'' -> 0` is exact
and `M'`, `M''` are of type `FP_n`, then `M` is of type `FP_n` (horseshoe
lemma on partial resolutions of length `n`). A direct summand of a module of
type `FP_n` is of type `FP_n`, because the criterion maps are additive.

**Step 3: the splitting.** Let `T` be the Bass--Serre tree. It is
contractible and carries an action of `H` without inversions whose quotient
is the finite graph. Its cellular chains give an exact sequence of left
`ZH`-modules
`0 -> ⊕_e Ind_{G_e}^H Z -> ⊕_v Ind_{G_v}^H Z -> Z -> 0`,
with `e` and `v` running over the finitely many edges and vertices of the
quotient graph. The left term is of type `FP_n` by Step 1, and `Z` is of type
`FP_n` because `H` is. By Step 2 the middle term is of type `FP_n`, and so is
each summand `Ind_{G_v}^H Z`. By Step 1 each `G_v` is of type `FP_n`.

**Step 4: retracts.** Let `G <= K` with a retraction `r: K -> G`,
`r ∘ i = id`. Functoriality of `Tor` in the pair (ring, module) gives maps
`Tor_k^{ZG}(∏ ZG, Z) -> Tor_k^{ZK}(∏ ZK, Z) -> Tor_k^{ZG}(∏ ZG, Z)` induced by
`i` and `r`. They compose to the identity and commute with the criterion
maps. So the criterion map for `G` is a retract of the one for `K`, and `G` is
of type `FP_n` whenever `K` is.
