import GroupApproximation.GGT.WPDAcylindricalHyperbolicity

/-!
# Dahmani--Guirardel--Osin's Corollary 6.12 and Theorem 6.14, reduced

`GGT.WPDAcylindricalHyperbolicity` carries four named literature propositions.
Two of them are the citations of Osin's Lemma 5.12: `DGOCorollary612` and
`DGOTheorem614`.  This module reduces both, from
Dahmani--Guirardel--Osin, *Hyperbolically embedded subgroups and rotating
families in groups acting on hyperbolic spaces*, Mem. Amer. Math. Soc. 245
(2017), arXiv:1111.7048.

## What the two theorems actually say

> **Corollary 6.12** (p. 93).  Let `G` be a group, `X ⊆ G`, `H ↪_h (G,X)` a
> non-degenerate subgroup.  Then for every `a ∈ G \ H` there exists `h ∈ H`
> such that `ah` is loxodromic and satisfies WPD with respect to the action on
> `Γ(G, X ⊔ H)`.

Its proof, in full, is three sentences: local finiteness plus infinitude makes
`(H, d̂)` unbounded; `|H^a ∩ H| < ∞` for `a ∉ H` is Proposition 4.33; and
**Theorem 6.11** then produces the element.  So 6.12 is not itself a leaf --- it
is a corollary of two other results, and this module proves it from them.

> **Theorem 6.14** (p. 94, §6.2).  Suppose that a group `G` contains a
> non-degenerate hyperbolically embedded subgroup.  Then (a) there is a maximal
> finite normal subgroup `K(G)`; (b) `K(G) ≤ H` for every infinite `H ↪_h G`;
> (c) for any `n` there is `H ≤ G` with `H ↪_h G` and `H ≅ Fₙ × K(G)`.

The repository's `DGOTheorem614` records only the consequence Osin's Lemma 5.12
uses --- `PingPong.FreeRankTwo G`, from (c) at `n = 2` --- but even that costs
the whole of §6.2: Lemmas 6.15--6.2x, on top of Corollary 6.12, Theorem 6.8 and
Propositions 4.14 and 4.33.

## The finding: Lemma 5.12 does not need Theorem 6.14

Osin's proof of Lemma 5.12 uses Theorem 6.14 for one thing only --- "*in
particular, `G` is not virtually cyclic*" --- which
`WPDAcylindricalHyperbolicity` then converts into "some element lies outside
`E(g)`" through a common-power-free pair.  **That element is already available
for free.**  Coning off `H` makes every element of `H` elliptic
(`RelGenSet.not_isLoxodromic_of_mem_fam`), while every element of `E(g)` of
infinite order shares a nonzero power with the loxodromic `g`
(`Elementary.exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder'`) and
so generates loxodromic powers.  An element of `H` of infinite order therefore
cannot lie in `E(g)`, and `g` together with its conjugate by that element is the
independent pair.

`actsNonElementarily_of_isLoxodromic_of_infiniteOrder_mem_fam` is that argument,
and `relativeCayleyNonElementary_of_612_of_infiniteOrder` is Lemma 5.12 from
`DGOCorollary612` alone, with **no appeal to Theorem 6.14 and no free subgroup**.

The infinite-order hypothesis it adds is free in the chain that consumes it:
`DGOTheorem68` returns a subgroup `E` containing `D.elt`, and `D.elt` is
loxodromic for the `(AH₃)` action, so `HullGeometry.not_isOfFinOrder_of_isLoxodromic`
makes it an element of infinite order of the peripheral subgroup.  What blocks
threading it today is the shape of `OsinAH4ToAH1`, which forgets `D.elt` between
`DGOTheorem68` and `RelativeCayleyNonElementary`; `OsinAH4ToAH1WithInfiniteOrder`
below is that statement with the datum kept.

## What is left, exactly

* `DGOTheorem611` --- the real content of Corollary 6.12.  Its proof occupies
  pp. 90--93 of the memoir and runs on the isolated-component machinery of §4.2,
  "Isolated components in geodesic polygons": the bound on an isolated component
  of an `n`-gon, together with Lemma 4.21.
* `DGOProposition433` --- almost malnormality.  Its proof is shorter: one
  geodesic quadrilateral `c = a⁻¹ p b q` built from a shortest word for `a`, in
  which the `H_λ`-edge `p` is isolated, and then the same bound at `n = 4`.

Both therefore rest on the same thing, and it is **already named in this
repository**: `GGT.OsinComponents.IsolatedComponentBound` is Osin's Lemma 4.2,
which he introduces as "*a simplified version of [DGO, Proposition 4.13]*" ---
that is, of the §4.2 bound.  `GGT/OsinComponents.lean` also supplies the
component vocabulary those proofs are written in (`IsComp`, `IsCompStart`,
`Connected`, `IsIsolated`, `vertex`, and the equivalence lemmas for
`Connected`).  What is *not* there is the polygon theory:
`IsolatedComponentBound` carries `IsQuasiGeodesicPolygon` as an abstract
predicate, so discharging either leaf means both instantiating that predicate
and building the quadrilateral (for 4.33) or the `(ahᵢ)^N` polygon (for 6.11)
against it.  The reduction to state is 4.33 and 6.11 *over*
`IsolatedComponentBound`, not over nothing.
* `PingPongFreeRankTwoGeometric` --- needed only for the free subgroup, not for
  Lemma 5.12.  `PingPong.PingPongFreeSubgroupGeometric` states this at `Type 0`
  and so cannot be applied to `Cayley D.alphabet` for `G : Type u`; the
  universe-polymorphic form is recorded here.
* The torsion case: if the peripheral subgroup is an infinite torsion group,
  `relativeCayleyNonElementary_of_612_of_infiniteOrder` does not apply and
  Theorem 6.14 is still needed.  That case does not arise in the chain above.

So `DGOCorollary612` and `DGOTheorem614` are both retired as *primitive*
citations: the first becomes a corollary, the second becomes unnecessary, and
the debt moves to `DGOTheorem611` and `DGOProposition433` --- with
Proposition 4.14 the single obstruction behind both.

## Checking the two new statements against the degenerate cases

Both leaves are stated so that the degenerate configurations Dahmani--Guirardel--Osin
exclude make them vacuous rather than false.

* `H = G` with `X = ∅`.  `Γ(G, X ⊔ H)` has diameter one, so nothing is
  loxodromic.  `DGOProposition433` is vacuous, there being no `a ∉ H`.
  `DGOTheorem611` is vacuous too, its `a` being asked for in `D.base = ∅`.
* `H` finite.  `DGOTheorem611`'s unboundedness hypothesis can still hold --- an
  element of `H` at infinite relative distance is not in any `relBall` --- which
  is why the hypothesis is written `¬ (H ⊆ relBall n)` and not "`H` is
  infinite": Dahmani--Guirardel--Osin's `d̂_λ` takes the value `∞`, and
  `o(H_λ) ≠ H_λ` in general (their Remark 6.10).
* `H` non-degenerate.  `not_subset_relBall_of_infinite` derives the
  unboundedness from infinitude exactly as the printed proof of Corollary 6.12
  does, and `exists_mem_base_notMem_fam` supplies the `a`, so both hypotheses of
  Theorem 6.11 are discharged and the corollary follows.

The `a` of Corollary 6.12 is taken in `D.base` rather than in `G \ H`.  The
printed corollary quantifies over all `a ∈ G \ H` and reaches Theorem 6.11's
`a ∈ X` through Corollary 4.27; the existence statement recorded here needs only
one `a`, and `exists_mem_base_notMem_fam` produces it in `D.base` outright ---
if every letter of `X` lay in `H` then so would every letter of the alphabet,
which generates.  So Corollary 4.27 is not a leaf of this reduction.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## The two leaves of Corollary 6.12 -/

/-- **Dahmani--Guirardel--Osin, Proposition 4.33(b)**, verbatim:

> For any `λ ∈ Λ` and any `g ∈ G \ H_λ`, the intersection `H_λ^g ∩ H_λ` has
> diameter at most `A` with respect to `d̂_λ`.  In particular, if
> `{H_λ}_{λ∈Λ} ↪_h G`, then `|H_λ ∩ H_λ^g| < ∞`.

Osin quotes it as "*hyperbolically embedded subgroups are almost malnormal*"
(his Proposition 2.10).  Only the "in particular" clause is recorded, and only
at a one-member family, which is the whole of what Corollary 6.12 consumes; the
diameter bound and the two-index part (a) are dropped.  `H^a ∩ H` is spelled
`{h | h ∈ H ∧ a⁻¹ h a ∈ H}`. -/
def DGOProposition433 : Prop :=
  ∀ (G : Type u) [Group G] (D : RelGenSet G Unit), D.IsHyperbolicallyEmbedded →
    ∀ a : G, a ∉ D.fam () →
      {h : G | h ∈ D.fam () ∧ a⁻¹ * h * a ∈ D.fam ()}.Finite

/-- **Dahmani--Guirardel--Osin, Theorem 6.11**:

> Suppose that a group `G` is weakly hyperbolic relative to `X` and `{H_λ}`.
> Assume that for some `λ` the following hold. (a) `H_λ` is unbounded with
> respect to `d̂_λ`.  (b) There exists `a ∈ X` such that `|H_λ^a ∩ H_λ| < ∞`.
> Then there exists `h ∈ H_λ` such that `ah` is a loxodromic element satisfying
> the WPD condition with respect to the action of `G` on `Γ(G, X ⊔ H)`.

Three weakenings, all in the safe direction.  The hypothesis is
`IsHyperbolicallyEmbedded` rather than the weaker "weakly hyperbolic relative
to"; the WPD conclusion is dropped, Corollary 6.12 as recorded in
`WPDAcylindricalHyperbolicity` asking only for loxodromy; and the "moreover"
clause, which produces `k` pairwise non-commensurable such elements under the
stronger hypothesis `o(H_λ)` unbounded, is dropped with it.

Clause (a) is written `∀ n, ¬ (H ⊆ relBall () n)`: unboundedness in `d̂` is
exactly the failure of every relative ball to contain `H`, and this form is
correct where a metric form would not be, because `d̂_λ` takes the value `∞`
(their Remark 6.10). -/
def DGOTheorem611 : Prop :=
  ∀ (G : Type u) [Group G] (D : RelGenSet G Unit), D.IsHyperbolicallyEmbedded →
    (∀ n : ℕ, ¬ ((D.fam () : Subgroup G) : Set G) ⊆ D.relBall () n) →
      ∀ a ∈ D.base, {h : G | h ∈ D.fam () ∧ a⁻¹ * h * a ∈ D.fam ()}.Finite →
        ∃ h ∈ D.fam (), IsLoxodromic (a * h) (Cayley.base D.alphabet)

/-- **Ping-pong, at the universes the DGO statements are written in.**  A group
acting on a hyperbolic space with two independent loxodromics contains a free
subgroup of rank two (Gromov, *Hyperbolic groups*, §8.2; Delzant).

`PingPong.PingPongFreeSubgroupGeometric` is this statement at `Type 0` in both
arguments, so it cannot be applied to `G : Type u` acting on
`Cayley D.alphabet`.  The content is identical; only the universes differ. -/
def PingPongFreeRankTwoGeometric : Prop :=
  ∀ (G : Type u) [Group G] (Y : Type v) [PseudoMetricSpace Y] [MulAction G Y]
    (δ : ℝ) (y : Y), IsIsometricAction G Y → IsHyperbolicSpace δ Y →
      ActsNonElementarily (⊤ : Subgroup G) y → PingPong.FreeRankTwo G

/-! ## The two hypotheses of Theorem 6.11, discharged -/

section Discharge

variable {G : Type u} [Group G]

/-- **A proper peripheral subgroup does not contain the base.**  If every letter
of `X` lay in `H` then, the letters of `H` lying in `H` trivially, the whole
alphabet would lie in `H`; but the alphabet generates `G`, so `H` would be
everything.

This is what lets Corollary 6.12 be proved without Dahmani--Guirardel--Osin's
Corollary 4.27: their `a` is taken anywhere in `G \ H` and moved into `X` by
enlarging the relative generating set, and one `a ∈ X \ H` is all the existence
statement needs. -/
theorem exists_mem_base_notMem_fam (D : RelGenSet G Unit)
    (hne : D.fam () ≠ ⊤) : ∃ a ∈ D.base, a ∉ D.fam () := by
  by_contra hcon
  push_neg at hcon
  apply hne
  have hsub : D.base ∪ ⋃ lam : Unit, ((D.fam lam : Subgroup G) : Set G)
      ⊆ ((D.fam () : Subgroup G) : Set G) := by
    rintro x (hx | hx)
    · exact hcon x hx
    · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hx
      cases lam
      exact hlam
  have hle : (⊤ : Subgroup G) ≤ D.fam () := by
    rw [← D.symmetricGenerating.closure_eq]
    exact (Subgroup.closure_le (D.fam ())).mpr hsub
  exact top_le_iff.mp hle

/-- **An infinite peripheral subgroup is unbounded in the relative metric.**
Local finiteness makes every relative ball finite, so no ball can contain an
infinite subgroup.  This is the step Dahmani--Guirardel--Osin open the proof of
Corollary 6.12 with: "*the local finiteness of `H` with respect to the metric
`d̂` implies that `(H, d̂)` is unbounded*". -/
theorem not_subset_relBall_of_infinite (D : RelGenSet G Unit)
    (hemb : D.IsHyperbolicallyEmbedded)
    (hinf : ((D.fam () : Subgroup G) : Set G).Infinite) (n : ℕ) :
    ¬ ((D.fam () : Subgroup G) : Set G) ⊆ D.relBall () n := by
  intro hsub
  exact hinf ((hemb.locallyFinite () n).subset hsub)

end Discharge

/-! ## Corollary 6.12, proved -/

/-- **Dahmani--Guirardel--Osin, Corollary 6.12, is a corollary.**  Their proof
is reproduced in full: unboundedness from local finiteness and infinitude, the
finite intersection from Proposition 4.33, and Theorem 6.11 then supplies the
element `ah`.

So `DGOCorollary612` is no longer a primitive citation of this development. -/
theorem dgoCorollary612_of (h611 : DGOTheorem611) (h433 : DGOProposition433) :
    DGOCorollary612 := by
  intro G _ D hemb hnd
  obtain ⟨a, haB, haH⟩ := exists_mem_base_notMem_fam D hnd.1
  obtain ⟨h, -, hlox⟩ :=
    h611 G D hemb (not_subset_relBall_of_infinite D hemb hnd.2) a haB
      (h433 G D hemb a haH)
  exact ⟨a * h, hlox⟩

/-! ## Lemma 5.12 without Theorem 6.14 -/

section NoFreeSubgroup

variable {G : Type u} [Group G]

/-- **An infinite-order peripheral element lies outside the elementary closure
of any loxodromic.**

Suppose `h ∈ H` has infinite order and lies in `E(g)` for a loxodromic `g`.
Then `h` shares a nonzero power with `g`
(`Elementary.exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder'`),
say `g ^ i = h ^ m` with `i, m ≠ 0`.  The left side is loxodromic, being a
nonzero power of a loxodromic; the right side lies in `H`, and coning off `H`
makes every element of `H` elliptic
(`RelGenSet.not_isLoxodromic_of_mem_fam`).

This is where Osin's "*`G` is not virtually cyclic*" comes from without
Theorem 6.14: the element outside `E(g)` is handed over by the peripheral
subgroup itself. -/
theorem notMem_elementaryClosure_of_mem_fam (D : RelGenSet G Unit) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley D.alphabet))
    (hacy : IsAcylindrical G (Cayley D.alphabet))
    {g : G} (hg : IsLoxodromic g (Cayley.base D.alphabet))
    {h : G} (hh : h ∈ D.fam ()) (hhinf : ¬ IsOfFinOrder h) :
    h ∉ Elementary.elementaryClosure g := by
  intro hmem
  obtain ⟨i, m, hi, hm, hpow⟩ :=
    Elementary.exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder'
      (isIsometricAction_cayley D.alphabet) hacy
      (ElementaryMorse.centralizerOrbitNearAxis_cayley_of_hyperbolic
        D.alphabet hδ)
      hg hmem hhinf
  have hglox : IsLoxodromic (g ^ i) (Cayley.base D.alphabet) :=
    isLoxodromic_zpow (isIsometricAction_cayley D.alphabet) hg hi
  rw [hpow] at hglox
  exact D.not_isLoxodromic_of_mem_fam () (Subgroup.zpow_mem hh m) hglox

/-- **Two independent loxodromics from one loxodromic and one infinite-order
peripheral element.**  The pair is `g` and its conjugate by the peripheral
element, which the previous lemma puts outside `E(g)`. -/
theorem actsNonElementarily_of_isLoxodromic_of_infiniteOrder_mem_fam
    (D : RelGenSet G Unit) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley D.alphabet))
    (hacy : IsAcylindrical G (Cayley D.alphabet))
    {g : G} (hg : IsLoxodromic g (Cayley.base D.alphabet))
    {h : G} (hh : h ∈ D.fam ()) (hhinf : ¬ IsOfFinOrder h) :
    ActsNonElementarily (⊤ : Subgroup G) (Cayley.base D.alphabet) :=
  Elementary.actsNonElementarily_of_notMem_elementaryClosure
    (isIsometricAction_cayley D.alphabet)
    (ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic
      D.alphabet hδ hacy)
    (Subgroup.mem_top g) (Subgroup.mem_top h) hg
    (notMem_elementaryClosure_of_mem_fam D hδ hacy hg hh hhinf)

end NoFreeSubgroup

/-- **Osin's Lemma 5.12 from Corollary 6.12 alone**, when the peripheral
subgroup has an element of infinite order.  `DGOTheorem614` does not appear, and
neither does any free subgroup. -/
theorem relativeCayleyNonElementary_of_612_of_infiniteOrder
    (h612 : DGOCorollary612) (G : Type u) [Group G] (D : RelGenSet G Unit)
    (hemb : D.IsHyperbolicallyEmbedded)
    (hacy : IsAcylindrical G (Cayley D.alphabet))
    (hnd : IsNonDegenerate (D.fam ()))
    (hord : ∃ h ∈ D.fam (), ¬ IsOfFinOrder h) :
    ActsNonElementarily (⊤ : Subgroup G) (Cayley.base D.alphabet) := by
  obtain ⟨δ, hδ⟩ := hemb.hyperbolic
  obtain ⟨g, hg⟩ := h612 G D hemb hnd
  obtain ⟨h, hh, hhinf⟩ := hord
  exact actsNonElementarily_of_isLoxodromic_of_infiniteOrder_mem_fam D hδ hacy
    hg hh hhinf

/-- **The free subgroup, when it is wanted anyway.**  Once the action is
non-elementary, ping-pong produces `F₂`; so the conclusion of `DGOTheorem614`
follows from Corollary 6.12 and ping-pong in the infinite-order case, without
any of §6.2.

Recorded because `PingPong.FreeRankTwo` has consumers of its own, not because
Lemma 5.12 needs it. -/
theorem freeRankTwo_of_612_of_infiniteOrder
    (hpp : PingPongFreeRankTwoGeometric) (h612 : DGOCorollary612)
    (G : Type u) [Group G] (D : RelGenSet G Unit)
    (hemb : D.IsHyperbolicallyEmbedded)
    (hacy : IsAcylindrical G (Cayley D.alphabet))
    (hnd : IsNonDegenerate (D.fam ()))
    (hord : ∃ h ∈ D.fam (), ¬ IsOfFinOrder h) :
    PingPong.FreeRankTwo G := by
  obtain ⟨δ, hδ⟩ := hemb.hyperbolic
  exact hpp G (Cayley D.alphabet) δ (Cayley.base D.alphabet)
    (isIsometricAction_cayley D.alphabet) hδ
    (relativeCayleyNonElementary_of_612_of_infiniteOrder h612 G D hemb hacy hnd
      hord)

/-! ## The datum the chain forgets -/

/-- **`OsinAH4ToAH1` with the infinite-order element kept.**

`DGOTheorem68` returns a subgroup `E` containing `D.elt`, and `D.elt` is
loxodromic, so it has infinite order by
`HullGeometry.not_isOfFinOrder_of_isLoxodromic`.  `OsinAH4ToAH1` forgets it
between there and `RelativeCayleyNonElementary`, which is the only reason
Lemma 5.12 has to be proved for a possibly-torsion peripheral subgroup and hence
the only reason `DGOTheorem614` is cited at all.  Keeping the datum costs one
hypothesis and is discharged at the call site by
`infiniteOrder_of_dgoTheorem68`. -/
def OsinAH4ToAH1WithInfiniteOrder : Prop :=
  ∀ (G : Type u) [Group G] (E : Subgroup G), E ≠ ⊤ → (E : Set G).Infinite →
    (∃ h ∈ E, ¬ IsOfFinOrder h) → IsHypEmbedded G E →
      IsAcylindricallyHyperbolic G

/-- **The datum is free.**  The subgroup `DGOTheorem68` produces contains the
loxodromic element of the `(AH₃)` data, and a loxodromic element has infinite
order. -/
theorem infiniteOrder_of_dgoTheorem68 {G : Type u} [Group G] (D : AH3Data G)
    {E : Subgroup G} (hmem : D.elt ∈ E) : ∃ h ∈ E, ¬ IsOfFinOrder h := by
  letI := D.metricSpace
  letI := D.mulAction
  exact ⟨D.elt, hmem, not_isOfFinOrder_of_isLoxodromic D.loxodromic⟩

/-! ## The chain with Theorem 6.14 retired

The two theorems below are the assembly `WPDAcylindricalHyperbolicity` cannot
carry: that file is imported *by* this one, so it cannot mention
`OsinAH4ToAH1WithInfiniteOrder` or `relativeCayleyNonElementary_of_612_of_infiniteOrder`.
They mirror `osinAH4ToAH1_of` and `osinTheorem12_of` line for line, with the
infinite-order element threaded through the same `D'.fam () = E` rewrite that
already carries properness and infinitude.

The result is `OsinTheorem12` --- the implication Minasyan--Osin cite as their
Theorem 3.3, and what `GGT.BassSerreDoubleHNN.minasyanOsinStatement_of_osin`
consumes --- from `DGOTheorem68`, `OsinTheorem54` and `DGOCorollary612`.
`DGOTheorem614` does not appear. -/

/-- **`(AH₄) ⇒ (AH₁)` with the infinite-order datum kept, and no free
subgroup.**  Osin's Theorem 5.4 supplies the alphabet, its clause (a) the
hyperbolicity and clause (b) the acylindricity, and Lemma 5.12 is
`relativeCayleyNonElementary_of_612_of_infiniteOrder` rather than
`relativeCayleyNonElementary_of`. -/
theorem osinAH4ToAH1WithInfiniteOrder_of (h54 : OsinTheorem54)
    (h612 : DGOCorollary612) : OsinAH4ToAH1WithInfiniteOrder := by
  intro G _ E hE hinf hord hemb
  obtain ⟨_X, D, -, hfam, hhyp⟩ := hemb
  obtain ⟨D', -, hfam', hhyp', hacy⟩ := h54 G D hhyp
  obtain ⟨δ, hδ⟩ := hhyp'.hyperbolic
  have hlam : D'.fam () = E := by
    rw [hfam']
    exact congrFun hfam ()
  have hEne : D'.fam () ≠ ⊤ := by rw [hlam]; exact hE
  have hEinf : ((D'.fam () : Set G)).Infinite := by rw [hlam]; exact hinf
  have hEord : ∃ h ∈ D'.fam (), ¬ IsOfFinOrder h := by rw [hlam]; exact hord
  exact ⟨⟨D'.alphabet, δ, hδ, hacy,
    relativeCayleyNonElementary_of_612_of_infiniteOrder h612 G D' hhyp' hacy
      ⟨hEne, hEinf⟩ hEord⟩⟩

/-- **Osin's Theorem 1.2, `(AH₃) ⇒ (AH₁)`, without Theorem 6.14.**  The
subgroup `DGOTheorem68` returns contains the loxodromic `D.elt`, which supplies
both the infinitude clause (`infinite_of_mem_of_isLoxodromic`) and the
infinite-order element (`infiniteOrder_of_dgoTheorem68`).

The two `letI`s are needed rather than decorative: `AH3Data`'s metric and action
are instance-implicit *fields*, and the type of `D.loxodromic` mentions them, so
without them the instance arguments of `infinite_of_mem_of_isLoxodromic` do not
resolve.  This is the shape of `osinTheorem12_of`. -/
theorem osinTheorem12_of_infiniteOrder (h68 : DGOTheorem68)
    (h4 : OsinAH4ToAH1WithInfiniteOrder) : OsinTheorem12 := by
  intro G _ D hnvc
  letI := D.metricSpace
  letI := D.mulAction
  obtain ⟨E, hmem, hne, hemb⟩ := h68 G D hnvc
  exact h4 G E hne (infinite_of_mem_of_isLoxodromic D.loxodromic hmem)
    (infiniteOrder_of_dgoTheorem68 D hmem) hemb

/-- **The three citations `OsinTheorem12` now costs.**  `DGOTheorem68`,
`OsinTheorem54` and `DGOCorollary612` --- and the last of these is itself a
corollary of `DGOTheorem611` and `DGOProposition433` by `dgoCorollary612_of`, so
the standing debt of this chain is four named statements, none of them
`DGOTheorem614`. -/
theorem osinTheorem12_of_612 (h68 : DGOTheorem68) (h54 : OsinTheorem54)
    (h612 : DGOCorollary612) : OsinTheorem12 :=
  osinTheorem12_of_infiniteOrder h68 (osinAH4ToAH1WithInfiniteOrder_of h54 h612)

end GGT
end GroupApproximation
