---
rg: 2
id: thompson-f-rigid-stabilizer-schreier-graphs-are-amenable-proof
kind: route
title: "Push F[a,b] to the ends by (F4); a diagonal limit of the conjugates contains F′, its Schreier graph is abelian, and Følner sets transfer back through the equivariant identification F/gHg⁻¹ ≅ F/H"
target: thompson-f-rigid-stabilizer-schreier-graphs-are-amenable
requires:
  - thompson-f-rigid-interval-subgroups-facts
  - thompson-f-commensurated-subgroups-are-trivial-or-normal
---

**Imports** (`thompson-f-rigid-interval-subgroups-facts`). (F1) `F′` is the set of elements supported in a
compact subset of `(0,1)`, and `F/F′ ≅ Z²`. (F2) For dyadic `a < b`, `F[a,b] ≅ F` with commutant `F(a,b)`
(the elements supported in a compact subset of `(a,b)`). (F4) `F′` is transitive on increasing tuples of
dyadic rationals in `(0,1)`. Also used: `g F[a,b] g⁻¹ = F[ga, gb]` (the conjugate is the identity outside
`g[a,b]`), `F` maps dyadics to dyadics, and `F` is finitely generated. From
`thompson-f-commensurated-subgroups-are-trivial-or-normal`: every nontrivial normal subgroup of `F`
contains `F′` (normal subgroups are commensurated).

**Convention (Chabauty convergence, elementary form).** For subgroups `K_n, K ≤ F` write `K_n → K` if for
every `x ∈ F`, eventually `x ∈ K_n ⇔ x ∈ K`.
- *Compactness.* Every sequence `K_n` has a convergent subsequence. Enumerate `F = {x_1, x_2, …}` (it is
  countable) and pass to nested subsequences on which membership of `x_1`, then `x_2`, … is constant; the
  diagonal subsequence converges to `K = {x : x ∈ K_n eventually}`. `K` is a subgroup: if `x, y ∈ K` then
  eventually `x, y ∈ K_n`, so `xy⁻¹ ∈ K_n` eventually, and membership of `xy⁻¹` stabilizes, so `xy⁻¹ ∈ K`.
- *Balls are local.* Let `B_r` be the ball of radius `r` in the word metric for `S`. The rooted labelled
  ball of radius `r` about the vertex `L` in `Sch(F/L)` is determined by `L ∩ B_(2r+1)`. Its vertices are
  the cosets `wL`, `w ∈ B_r`, with `wL = w′L ⇔ w⁻¹w′ ∈ L` and `|w⁻¹w′| ≤ 2r`; its edges `s·wL = w′L` hold
  iff `w′⁻¹ s w ∈ L`, of length `≤ 2r + 1`.

**Lemma 1 (transfer).** If `K_n → K` with `K_n` conjugates of `H`, and `Sch(F/K)` is amenable, then
`Sch(F/H)` is amenable.

*Proof.* Fix `ε > 0` and a finite `A ⊆ F/K` with `|∂A| ≤ ε|A|`, where `∂A` is the set of edges `(v, sv)`
with `v ∈ A`, `s ∈ S`, `sv ∉ A`. If `F/K` is infinite, `Sch(F/K)` is connected, so `A ⊆` the ball of some
radius `r` about the vertex `K`, and `A` and `∂A` are read inside the ball of radius `r+1`, which by the
convention is determined by `K ∩ B_(2r+3)`. This is a finite set of membership conditions, so for large `n`
the balls of radius `r+1` about the root in `Sch(F/K)` and in `Sch(F/K_n)` are isomorphic as rooted
labelled graphs. The image `A_n` of `A` has `|A_n| = |A|` and `|∂A_n| = |∂A|`. Write `K_n = gHg⁻¹`. The map
`x·gHg⁻¹ ↦ xgH` is well defined (`x g h g⁻¹ · g H = xgH`), bijective and `F`-equivariant, hence a labelled
graph isomorphism `Sch(F/K_n) ≅ Sch(F/H)`. So `Sch(F/H)` has a set with `|∂| ≤ ε|·|`. If `F/K` is finite,
take `A = F/K`, `∂A = ∅`, and argue the same way with `r` its diameter: for large `n`, `Sch(F/K_n)` contains
a copy of the closed ball with no outgoing edges, which by connectedness is all of `Sch(F/K_n)`, so
`F/H` is finite and amenable. ∎

**Theorem A.** If `H ⊇ F[a,b]` for some dyadic `a < b`, then `Sch(F/H)` is amenable.

*Proof.*
1. *Interior interval.* Choose dyadic `a < a′ < b′ < b` with `0 < a′`, `b′ < 1`. Then `F[a′,b′] ⊆ F[a,b] ⊆ H`.
2. *Push to the ends.* For `n ≥ 1` the pair `2^(−n−1) < 1 − 2^(−n−1)` is an increasing dyadic pair in
   `(0,1)`, so by (F4) there is `g_n ∈ F′` with `g_n a′ = 2^(−n−1)` and `g_n b′ = 1 − 2^(−n−1)`. Then
   `K_n := g_n H g_n⁻¹ ⊇ F[2^(−n−1), 1 − 2^(−n−1)] =: E_n`, and `E_1 ⊆ E_2 ⊆ …`.
3. *The limit contains F′.* Pass to a convergent subsequence `K_n → K`. Let `x ∈ F′`. By (F1) `x` is
   supported in a compact subset of `(0,1)`, hence in some `[2^(−N−1), 1 − 2^(−N−1)]`, so `x ∈ E_n ⊆ K_n` for
   all `n ≥ N` along the subsequence, and `x ∈ K`. So `K ⊇ F′`.
4. *The limit graph is abelian.* `K ⊇ F′` is normal (it is the preimage of a subgroup of `F/F′`), and `F/K`
   is a quotient of `F/F′ ≅ Z²`. So `Sch(F/K)` is the Cayley graph of the finitely generated abelian group
   `F/K` for the image of `S`. It is amenable: each `s ∈ S` maps to an element of word length at most `c`
   in the images of the two standard generators of `Z²`, so the balls `B_m` of `Sch(F/K)` satisfy
   `|B_m| ≤ (2cm + 1)²`. If `|B_(m+1)| ≥ (1 + ε)|B_m|` held for all `m ≥ m_0`, growth would be exponential;
   so for every `ε` some `m` has `|B_(m+1) ∖ B_m| < ε|B_m|`, and `|∂B_m| ≤ |S| · |B_(m+1) ∖ B_m|`.
5. *Transfer.* By Lemma 1, `Sch(F/H)` is amenable. ∎

**Theorem A′.** For `H ≤ F`, the following are equivalent: (1) `H ⊇ F[a,b]` for some dyadic `a < b`;
(2) `H` contains a nontrivial normal subgroup `N` of some `F[a,b]`; (3) some limit of conjugates of `H`
contains `F′`.

*Proof.*
- (1) ⇒ (2): take `N = F[a,b]`.
- (2) ⇒ (1): transport the normal-subgroup fact through `F[a,b] ≅ F` (F2): `N` contains the commutant of
  `F[a,b]`, which is `F(a,b)`. For dyadic `a < a′ < b′ < b`, `F[a′,b′] ⊆ F(a,b) ⊆ N ⊆ H`.
- (1) ⇒ (3): Steps 1–3 of Theorem A.
- (3) ⇒ (1): let `g_n H g_n⁻¹ → K ⊇ F′`. `F[1/4,3/4] ⊆ F′` is isomorphic to `F` (F2), hence generated by
  finitely many `x_1, …, x_r`. For large `n` all `x_i ∈ g_n H g_n⁻¹`, so
  `g_n⁻¹ F[1/4,3/4] g_n = F[g_n⁻¹(1/4), g_n⁻¹(3/4)] ⊆ H`, with dyadic endpoints in increasing order. ∎

**Instances checked.**
- If `C ⊆ [0,1]` is not dense, its complement contains a dyadic interval `[a,b]`, and `F[a,b]` fixes `C`
  pointwise, so it lies in both the pointwise and the setwise stabilizer.
- If a Borel set `B ⊇ [a,b]`, then `F[a,b]` maps `B` to `B`. If `μ([a,b]) = 0`, then `g_*μ = μ` for
  `g ∈ F[a,b]`, since `g⁻¹` is the identity off the null set `[a,b]`.
- A confined subgroup contains `St0_F′(S)` for a finite `S`
  (`thompson-f-confined-subgroups-fix-finite-sets`, Theorem 3.1), and that contains `F[a,b]` for any
  dyadic `[a,b] ⊆ (0,1) ∖ S`.
- A nontrivial commensurated subgroup contains `F′ ⊇ F[1/4,3/4]`.

**Calibration.** The hypothesis cannot be dropped: `H = 1` gives the Cayley graph, whose amenability is the
root. The proof uses only that conjugates of one rigid interval subgroup exhaust `F′` and that `F/F′` is
abelian; it gives no information about subgroups containing no `F[a,b]`, which include every amenable
subgroup.
