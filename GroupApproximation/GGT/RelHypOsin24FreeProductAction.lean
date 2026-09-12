import GroupApproximation.GGT.RelHypOsin24Action
import GroupApproximation.GGT.RelHypFreeProductAcylindrical
import GroupApproximation.GGT.RelHypSuitabilityResidue
import GroupApproximation.GGT.HullSCUnionGeometryHyperbolicFactor
import GroupApproximation.GGT.HullSCUnionGeometryLongSyllable

/-!
# The compatible Hull action for the Fournier--Facio free product

The general relatively hyperbolic action bridge is not needed for the
Fournier--Facio input.  Its ambient group is `U ∗ H`, its sole peripheral is
the factor `U`, and its suitable subgroup is the image of `H`.

At a finite hyperbolic alphabet `S` of `H`, the relative Cayley alphabet is
the union of all of `U` and `S`.  The previous module proves acylindricity of
that exact action, while the free-product four-point theorem proves
hyperbolicity.  The partner factor embeds isometrically.  Thus the two
infinite-order, non-commensurable witnesses already contained in Osin
suitability become independent loxodromics, and the partner image is suitable
in Hull's sense on the same alphabet.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid Monoid.CoprodI
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductUnionNorm
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- The partner factor is isometrically embedded in the coned free-product
alphabet. -/
theorem wordDist_freeProductPartnerHom_eq
    (U H : Type) [Group U] [Group H]
    (S : Finset H) (hS : IsSymmetricGeneratingSet (S : Set H))
    (x y : H) :
    wordDist (freeProductLabelledRelGen U H S hS).alphabet.carrier
        (freeProductPartnerHom U H x) (freeProductPartnerHom U H y) =
      wordDist (S : Set H) x y := by
  classical
  have hfactor : ∀ b : Bool,
      IsSymmetricGeneratingSet (conedFactorAlphabet U H S b) :=
    isSymmetricGeneratingSet_conedFactorAlphabet U H hS
  have hcarrier :
      (freeProductLabelledRelGen U H S hS).alphabet.carrier =
        unionCarrier (conedFactorAlphabet U H S) := by
    change (freeProductRelGen U H S hS).alphabet.carrier = _
    exact alphabet_carrier_freeProductRelGen U H S hS
  unfold wordDist
  rw [← map_inv, ← map_mul, hcarrier]
  exact HullSCUnionGeometry.wordNorm_of_single_eq
    (i := true) hfactor (x⁻¹ * y)

/-- Infinite order of a partner image reflects to the partner. -/
theorem not_isOfFinOrder_partner_of_image_powers
    {U H : Type} [Group U] [Group H] {y : H}
    (hord : ∀ n : ℕ, 0 < n → (freeProductPartnerHom U H y) ^ n ≠ 1) :
    ¬ IsOfFinOrder y := by
  intro hfin
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  apply hord n hn
  rw [← map_pow, hpow, map_one]

/-- Non-commensurability of partner images rules out a direct common power in
the partner. -/
theorem noCommonZpow_partner_of_not_osinCommensurable
    {U H : Type} [Group U] [Group H] {x y : H}
    (hnc : ¬ OsinCommensurable (freeProductPartnerHom U H x)
      (freeProductPartnerHom U H y)) :
    ∀ p q : ℤ, p ≠ 0 → q ≠ 0 → x ^ p ≠ y ^ q := by
  intro p q hp hq heq
  apply hnc
  refine ⟨p, q, 1, hp, hq, ?_⟩
  simp only [inv_one, one_mul, ← map_zpow, heq, mul_one]

/-- **The compatible relative Hull data for the free-product application.**

This is the precise `Unit`-family action used by Fournier--Facio Proposition
2.3.  It requires no action theorem for an arbitrary relatively hyperbolic
family. -/
theorem nonempty_relativeHullData_freeProduct
    (U H : Type) [Group U] [Group H]
    (hhyp : Hyperbolic.IsHyperbolicGroup H)
    (hsuit : IsSuitableSubgroup
      (fun _ : Unit => freeProductPeripheral U H)
      (MonoidHom.range (freeProductPartnerHom U H))) :
    Nonempty (RelativeHullData
      (fun _ : Unit => freeProductPeripheral U H)
      (MonoidHom.range (freeProductPartnerHom U H))) := by
  obtain ⟨S, hS, delta, hdelta⟩ := hhyp
  let D : RelGenSet (CoprodI (pairFamily U H)) Unit :=
    freeProductLabelledRelGen U H S hS
  have hfinite : D.base.Finite := (freeProductRelGen U H S hS).finite
  have hfam : D.fam = (fun _ : Unit => freeProductPeripheral U H) := rfl
  have hemb : D.IsHyperbolicallyEmbedded := by
    refine ⟨?_, pairLabelledRelGen_locallyFinite
      (G := pairFamily U H) S hS⟩
    exact ⟨(max delta 1 : ℕ),
      isHyperbolicSpace_cayley_of_fourPoint D.alphabet
        (isFourPointHyperbolic_freeProductRelGen U H S hS hdelta)⟩
  have hnormal : HullSuitable.NormalizesNoNontrivialFinite
      (MonoidHom.range (freeProductPartnerHom U H)) :=
    IsSuitableSubgroup.normalizesNoNontrivialFinite hsuit
  obtain ⟨f₁, hf₁, f₂, hf₂, _hhyper₁, _hhyper₂,
    hord₁, hord₂, hnc, _hinter⟩ := hsuit
  obtain ⟨y₁, hy₁⟩ := hf₁
  obtain ⟨y₂, hy₂⟩ := hf₂
  subst f₁
  subst f₂
  let B : Alphabet H := ⟨(S : Set H), hS⟩
  have hBdelta : IsHyperbolicSpace (delta : ℝ) (Cayley B) :=
    isHyperbolicSpace_cayley_of_fourPoint B hdelta
  have hBfinite : B.carrier.Finite := S.finite_toSet
  have hy₁Infinite : ¬ IsOfFinOrder y₁ :=
    not_isOfFinOrder_partner_of_image_powers hord₁
  have hy₂Infinite : ¬ IsOfFinOrder y₂ :=
    not_isOfFinOrder_partner_of_image_powers hord₂
  have hy₁Lox : IsLoxodromic y₁ (Cayley.base B) :=
    HullSCUnionGeometry.isLoxodromic_cayley_of_not_isOfFinOrder
      B hBfinite hBdelta hy₁Infinite
  have hy₂Lox : IsLoxodromic y₂ (Cayley.base B) :=
    HullSCUnionGeometry.isLoxodromic_cayley_of_not_isOfFinOrder
      B hBfinite hBdelta hy₂Infinite
  have hnoPower : ∀ p q : ℤ, p ≠ 0 → q ≠ 0 → y₁ ^ p ≠ y₂ ^ q :=
    noCommonZpow_partner_of_not_osinCommensurable hnc
  have hBacy : IsAcylindrical H (Cayley B) :=
    isAcylindrical_cayley_of_finite B hBfinite
  have hindTheory : Elementary.IndependentOfNoCommonZpow H (Cayley.base B) :=
    HullSCUnionGeometry.independentOfNoCommonZpow_cayley_of_acylindrical
      B hBdelta hBacy
  have hind : Independent y₁ y₂ (Cayley.base B) :=
    hindTheory y₁ y₂ hy₁Lox hy₂Lox hnoPower
  have hpartnerNE : ActsNonElementarily (⊤ : Subgroup H) (Cayley.base B) :=
    ⟨y₁, Subgroup.mem_top y₁, y₂, Subgroup.mem_top y₂,
      hy₁Lox, hy₂Lox, hind⟩
  have hisometric : ∀ x y : H,
      wordDist D.alphabet.carrier (freeProductPartnerHom U H x)
          (freeProductPartnerHom U H y) = wordDist B.carrier x y :=
    wordDist_freeProductPartnerHom_eq U H S hS
  have hactsPartner : ActsNonElementarily
      (MonoidHom.range (freeProductPartnerHom U H))
      (Cayley.base D.alphabet) :=
    HullSC.actsNonElementarily_range_of_wordDist_eq
      (freeProductPartnerHom U H) hisometric hpartnerNE
  have hactsTop : ActsNonElementarily
      (⊤ : Subgroup (CoprodI (pairFamily U H))) (Cayley.base D.alphabet) :=
    HullSC.actsNonElementarily_top_of_subgroup hactsPartner
  have hacy : IsAcylindrical (CoprodI (pairFamily U H))
      (Cayley D.alphabet) :=
    isAcylindrical_freeProductLabelledRelGen U H S hS
  obtain ⟨Delta, hDelta⟩ := hemb.hyperbolic
  let A : HullGeneratingSet (CoprodI (pairFamily U H)) :=
    { alphabet := D.alphabet
      delta := Delta
      hyperbolic := hDelta
      acylindrical := hacy
      nonElementary := hactsTop }
  have hHullSuitable : Suitable A.alphabet
      (MonoidHom.range (freeProductPartnerHom U H)) :=
    ⟨hactsPartner, hnormal⟩
  exact ⟨{
    rel := D
    base_finite := hfinite
    fam_eq := hfam
    embedded := hemb
    hull := A
    hull_alphabet := rfl
    suitable := hHullSuitable }⟩

end RelHyp
end GGT
end GroupApproximation
