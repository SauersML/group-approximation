import GroupApproximation.GGT.ElementaryBowditchProof
import GroupApproximation.GGT.ElementaryOsinSNormal
import GroupApproximation.GGT.CayleyGeodesicQuotient
import GroupApproximation.GGT.CayleyGeodesicRealisation
import GroupApproximation.GGT.HyperbolicFreeGroupAH
import GroupApproximation.GGT.HullSCUnionGeometryCoprod

/-!
# A Hull generating set on a hyperbolic group, and what it still costs

`GGT/HullSCUnionGeometryCoprod.hullGeneratingSetOfHyperbolic` builds a
`HullGeneratingSet` on a hyperbolic group out of its finite alphabet, once
non-elementarity of the translation action is supplied.  This module reduces
that last field to two purely algebraic witnesses:

> an element `g` of infinite order, and an element `t` outside its elementary
> closure `E(g)`.

`actsNonElementarily_cayley_of_finite` is that reduction, and
`hullGeneratingSetOfWitness` packages it.

## Why the reduction is not circular

The two geometric inputs of Osin's theory --- Bowditch's dichotomy
(`GGT.escapingIsLoxodromic_of_geodesic`, Osin's Theorem 1.1) and the
common-power criterion for independence
(`GGT.ElementaryMorse.independentOfNoCommonZpow_of_geodesic`, Osin's Lemma 6.5
and Corollary 6.6) --- are already theorems of this repository in a geodesic
hyperbolic space carrying an acylindrical isometric action.  What the repository
lacks is a way to *reach* them at a Cayley graph without already having a
`HullGeneratingSet`: `GGT.escapingIsLoxodromic_cayley` and
`GGT.ElementaryMorse.independentOfNoCommonZpow_cayley` both consume one, and its
third field is exactly the non-elementarity being proved.

`hasGeodesicModel_of_alphabet` removes that circularity.  The metric realisation
of `Γ(G,A)` needs only hyperbolicity of the vertex metric --- geodesicity is
`GGT.CayleyGeodesicModel.isGeodesicRealisationQuot`, read on the metric
identification `PointQuot A`, because `Point A` carries a pseudometric whose
doubled edges put distinct points at distance zero and so admits no on-the-nose
geodesic --- so the model, and with it both of Osin's theorems, is
available as soon as the Cayley graph is hyperbolic and the action on it is
acylindrical.  For a *finite* alphabet the second is
`GGT.isAcylindrical_cayley_of_finite`: a proper action is acylindrical.

## The one new estimate

`isEscaping_cayley_of_not_isOfFinOrder`: over a finite alphabet an element of
infinite order escapes every ball.  The powers of such an element are distinct
and each ball is finite, so only finitely many powers lie in any one ball.  This
is where properness --- and only properness --- is used, and it is what turns
Bowditch's dichotomy into

> in a hyperbolic group, every element of infinite order is loxodromic on the
> Cayley graph of a finite alphabet

(`isLoxodromic_cayley_of_not_isOfFinOrder`), with no further input.
-/

namespace GroupApproximation
namespace HullSCUnionGeometry

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## 1.  The geodesic model, before non-elementarity is known -/

/-- **The metric realisation of `Γ(G,A)` needs only hyperbolicity of the vertex
metric.**  `GGT.CayleyGeodesicRealisation.hasGeodesicModel_of_hullGeneratingSet`
is this statement with a `HullGeneratingSet` in place of `A` and `hδ`; the
`HullGeneratingSet` packaging is exactly what cannot be assumed while
non-elementarity is still being proved. -/
theorem hasGeodesicModel_of_alphabet {G : Type u} [Group G] (A : Alphabet G)
    {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A)) :
    Manuscript.NonMF.AxisDichotomyRoute.HasGeodesicModel A :=
  ⟨GGT.CayleyGeodesicModel.modelQuot A hδ
    (GGT.Elementary.nonneg_of_isHyperbolicSpace hδ (Cayley.base A))
    (GGT.CayleyGeodesicModel.isGeodesicRealisationQuot A)⟩

/-! ## 2.  Osin's two theorems at any hyperbolic acylindrical alphabet -/

/-- **Bowditch's dichotomy at `Γ(G,A)`**, from hyperbolicity and acylindricity
alone.  The same proof as `GGT.escapingIsLoxodromic_cayley`, with the
`HullGeneratingSet` replaced by its two geometric fields. -/
theorem escapingIsLoxodromic_cayley_of_acylindrical {G : Type u} [Group G]
    (A : Alphabet G) {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A))
    (hacyl : IsAcylindrical G (Cayley A)) :
    GGT.Elementary.EscapingIsLoxodromic G (Cayley.base A) := by
  obtain ⟨M⟩ := hasGeodesicModel_of_alphabet A hδ
  have hacyW : IsAcylindrical G M.W :=
    GGT.isAcylindrical_of_additiveDistortion_of_dense M.distortion_nonneg
      M.hasAdditiveDistortion M.hasDenseImage M.equivariant M.isometric hacyl
  exact GGT.Elementary.escapingIsLoxodromic_of_map M.distortion_nonneg
    M.hasAdditiveDistortion M.equivariant
    (GGT.escapingIsLoxodromic_of_geodesic M.hyperbolic M.delta_nonneg M.geodesic
      M.isometric hacyW _)

/-- **Osin's Lemma 6.5 and Corollary 6.6 at `Γ(G,A)`**, from hyperbolicity and
acylindricity alone: two loxodromics with no common nonzero power are
independent. -/
theorem independentOfNoCommonZpow_cayley_of_acylindrical {G : Type u} [Group G]
    (A : Alphabet G) {δ : ℝ} (hδ : IsHyperbolicSpace δ (Cayley A))
    (hacyl : IsAcylindrical G (Cayley A)) :
    GGT.Elementary.IndependentOfNoCommonZpow G (Cayley.base A) := by
  obtain ⟨M⟩ := hasGeodesicModel_of_alphabet A hδ
  have hacyW : IsAcylindrical G M.W :=
    GGT.isAcylindrical_of_additiveDistortion_of_dense M.distortion_nonneg
      M.hasAdditiveDistortion M.hasDenseImage M.equivariant M.isometric hacyl
  exact GGT.Elementary.independentOfNoCommonZpow_of_map M.distortion_nonneg
    M.hasAdditiveDistortion M.equivariant
    (GGT.ElementaryMorse.independentOfNoCommonZpow_of_geodesic M.hyperbolic
      M.delta_nonneg M.geodesic M.isometric hacyW _)

/-! ## 3.  Properness: an infinite-order element escapes a finite alphabet -/

/-- **The powers of an element of infinite order are distinct.** -/
theorem injective_pow_of_not_isOfFinOrder {G : Type u} [Group G] {g : G}
    (hg : ¬ IsOfFinOrder g) : Function.Injective (fun n : ℕ => g ^ n) := by
  have hz : Function.Injective (fun n : ℤ => g ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr hg
  intro m n hmn
  have hcast : g ^ (m : ℤ) = g ^ (n : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact hmn
  exact Nat.cast_injective (hz hcast)

/-- **An element of infinite order escapes every ball of a finite alphabet.**

Each ball of `Γ(G,A)` about the basepoint is finite (`GGT.wordNorm_ball_finite`)
and the powers of `g` are distinct, so only finitely many of them lie in any one
ball; past the largest such exponent every power is outside it.  This is the
only place properness of the action is used. -/
theorem isEscaping_cayley_of_not_isOfFinOrder {G : Type u} [Group G]
    (A : Alphabet G) (hfin : A.carrier.Finite) {g : G} (hg : ¬ IsOfFinOrder g) :
    IsEscaping g (Cayley.base A) := by
  have hinj := injective_pow_of_not_isOfFinOrder hg
  show Filter.Tendsto (fun n : ℕ => dist (Cayley.base A) ((g ^ n) • Cayley.base A))
    Filter.atTop Filter.atTop
  rw [Filter.tendsto_atTop]
  intro R
  have hball : {x : G | wordNorm A.carrier x ≤ ⌈R⌉₊}.Finite :=
    GGT.wordNorm_ball_finite A.symmetricGenerating hfin ⌈R⌉₊
  have hpre : ((fun n : ℕ => g ^ n) ⁻¹'
      {x : G | wordNorm A.carrier x ≤ ⌈R⌉₊}).Finite :=
    Set.Finite.preimage (fun a _ b _ h => hinj h) hball
  obtain ⟨N, hN⟩ := hpre.bddAbove
  rw [Filter.eventually_atTop]
  refine ⟨N + 1, fun n hn => ?_⟩
  have hnot : n ∉ ((fun n : ℕ => g ^ n) ⁻¹'
      {x : G | wordNorm A.carrier x ≤ ⌈R⌉₊}) := by
    intro hmem
    have hle : n ≤ N := hN hmem
    omega
  have hgt : ⌈R⌉₊ < wordNorm A.carrier (g ^ n) := by
    by_contra hle
    exact hnot (not_lt.mp hle)
  have hdist : dist (Cayley.base A) ((g ^ n) • Cayley.base A)
      = ((wordNorm A.carrier (g ^ n) : ℕ) : ℝ) := by
    rw [HullSC.cayleyDist_base_smul, wordDist_one_left]
  rw [hdist]
  have h1 : R ≤ ((⌈R⌉₊ : ℕ) : ℝ) := Nat.le_ceil R
  have h2 : ((⌈R⌉₊ : ℕ) : ℝ) < ((wordNorm A.carrier (g ^ n) : ℕ) : ℝ) := by
    exact_mod_cast hgt
  linarith

/-- **In a hyperbolic group every element of infinite order is loxodromic on the
Cayley graph of a finite alphabet.**  Escape is properness; escape to loxodromy
is Bowditch's dichotomy. -/
theorem isLoxodromic_cayley_of_not_isOfFinOrder {G : Type u} [Group G]
    (A : Alphabet G) (hfin : A.carrier.Finite) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A)) {g : G} (hg : ¬ IsOfFinOrder g) :
    IsLoxodromic g (Cayley.base A) :=
  escapingIsLoxodromic_cayley_of_acylindrical A hδ
    (GGT.isAcylindrical_cayley_of_finite A hfin) g
    (isEscaping_cayley_of_not_isOfFinOrder A hfin hg)

/-! ## 4.  Non-elementarity from two algebraic witnesses -/

/-- **Two independent loxodromics, from one element of infinite order and one
element outside its elementary closure.**

`g` is loxodromic by the previous theorem; `t g t⁻¹` is its conjugate, hence
loxodromic; and the two are independent because a common nonzero power of `g`
and `t g t⁻¹` is exactly a witness for `t ∈ E(g)`
(`GGT.Elementary.actsNonElementarily_of_notMem_elementaryClosure`, against the
common-power criterion supplied above). -/
theorem actsNonElementarily_cayley_of_finite {G : Type u} [Group G]
    (A : Alphabet G) (hfin : A.carrier.Finite) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A)) {g t : G} (hg : ¬ IsOfFinOrder g)
    (ht : t ∉ GGT.Elementary.elementaryClosure g) :
    ActsNonElementarily (⊤ : Subgroup G) (Cayley.base A) :=
  GGT.Elementary.actsNonElementarily_of_notMem_elementaryClosure
    (isIsometricAction_cayley A)
    (independentOfNoCommonZpow_cayley_of_acylindrical A hδ
      (GGT.isAcylindrical_cayley_of_finite A hfin))
    (Subgroup.mem_top g) (Subgroup.mem_top t)
    (isLoxodromic_cayley_of_not_isOfFinOrder A hfin hδ hg) ht

/-! ## 5.  The Hull generating set, and the residue it leaves -/

/-- **A Hull generating set on a hyperbolic group, from two algebraic
witnesses.**  All three fields are now theorems: hyperbolicity of `Γ(H,T)` is
the four-point condition of `T`, acylindricity is properness, and
non-elementarity is `actsNonElementarily_cayley_of_finite`. -/
noncomputable def hullGeneratingSetOfWitness {H : Type} [Group H] {T : Finset H}
    (hT : IsSymmetricGeneratingSet (T : Set H)) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic (T : Set H) δ) {g t : H}
    (hg : ¬ IsOfFinOrder g) (ht : t ∉ GGT.Elementary.elementaryClosure g) :
    HullGeneratingSet H :=
  hullGeneratingSetOfHyperbolic hT hδ
    (actsNonElementarily_cayley_of_finite (⟨(T : Set H), hT⟩ : Alphabet H)
      T.finite_toSet (GGT.isHyperbolicSpace_cayley_of_fourPoint _ hδ) hg ht)

/-- **`HullSC.FreeProductUnionGeometryStatement` from the acylindricity of the
union alphabet and two algebraic witnesses in `H`.**

This is `freeProductUnionGeometryStatement_of` with its second hypothesis
weakened from "`H` has a Hull generating set" to

> `H` has an element `g` of infinite order and an element `t ∉ E(g)`,

which is all that the geometry now needs.  The first hypothesis --- acylindricity
of the translation action on `Γ(E ∗ H, A ⊔ B)` --- is unchanged, and is the
tree-of-spaces crossing estimate. -/
theorem freeProductUnionGeometryStatement_of_witness
    (hacyl : ∀ (E H : Type) [Group E] [Group H] (A : HullGeneratingSet E)
      (B : HullGeneratingSet H),
        IsAcylindrical (Monoid.Coprod E H)
          (Cayley (HullSC.unionAlphabet A.alphabet B.alphabet)))
    (hwit : ∀ (H : Type) [Group H], Infinite H →
      GroupApproximation.Hyperbolic.IsHyperbolicGroup H →
        HasKazhdanPropertyT.{0, 0} H →
          ∃ g t : H, ¬ IsOfFinOrder g ∧
            t ∉ GGT.Elementary.elementaryClosure g) :
    HullSC.FreeProductUnionGeometryStatement := by
  refine freeProductUnionGeometryStatement_of hacyl ?_
  intro H instH hinf hhyp hKT
  letI := instH
  obtain ⟨g, t, hg, ht⟩ := hwit H hinf hhyp hKT
  obtain ⟨T, hTsym, δ, hδ⟩ := hhyp
  exact ⟨hullGeneratingSetOfWitness hTsym hδ hg ht⟩

end HullSCUnionGeometry
end GroupApproximation
