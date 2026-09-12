import GroupApproximation.CharClass.ThomHabs
import GroupApproximation.CharClass.ThomChernDegreewiseOf
import GroupApproximation.CharClass.ThomDataOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Thom data of the pair from two Leray–Hirsch instances, over any commutative ring

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

At `F₂` the chain `ThomRestrictSquare → ThomHabs → ThomDataFromLH` produces the degreewise
Thom data of the pair `(P, Z)`, the second hypothesis of `LIXThomDatum`, from a
Leray–Hirsch instance on `P` of rank `r + 1` and one on `Z` of rank `r`:

1. the restriction of the pair, in Leray–Hirsch coordinates, is `ThomDeg.restrictMap` at
   multiplication by the Chern coefficients (`absToSub_sum_lhTermOf`);
2. so the coordinate image of the relative group is the kernel of that map
   (`range_thomJm_eq_ker_restrictMapOf`), by exactness at the absolute group;
3. `relToAbs` is injective because the restriction one degree below the top is onto
   (`relToAbs_injective_of_gradedOf`).

Every step is linear algebra over the coefficient ring, apart from one line of the `F₂`
file: `LIXThomLH.lhSumTop` proves scalar linearity by `decide` over `ZMod 2`.  Here that is
`lhTerm_smulOf`, from naturality of pullback and cup product in the scalar.  The
coefficient equivalence `lhTopEquivOf` of the top absolute group is built from
`lix-coeff`'s `LHCast.bijective_sum_lhTerm_topOf`.

## Main declarations

* `lhTerm_smulOf`, `lhSumTopOf`, `lhTopEquivOf` — the top coefficient equivalence over `K`.
* `absToSub_sum_lhTermOf` — the restriction square over `K`.
* `range_comp_eq_ker_of_squareOf` — the algebra, over `K`.
* `range_thomJm_eq_ker_restrictMapOf` — `habs` over `K`.
* `relToAbs_injective_of_gradedOf` — `hinj0` over `K`.
* `thomData_of_lerayHirschOf` — **the degreewise Thom data over `K`**, with nothing left
  named.
-/

set_option autoImplicit false

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {K : Type} [CommRing K] {X P : TopCat.{0}}

/-! ## 1. The top coefficient equivalence over `K` -/

/-- A column term is `K`-linear in its coefficient. -/
theorem lhTerm_smulOf (π : P ⟶ X) (ξ : Hmod K P 2) (n i : ℕ) (c : K)
    (a : Hmod K X (n - 2 * i)) : lhTerm π ξ n i (c • a) = c • lhTerm π ξ n i a := by
  by_cases h : 2 * i ≤ n
  · rw [lhTerm_of_le π ξ h, lhTerm_of_le π ξ h, pull_smul, cup_smul_left, cohCast_smul]
  · rw [lhTerm_of_gt π ξ h, lhTerm_of_gt π ξ h, smul_zero]

/-- The coefficient combination at the top degree, as a `K`-linear map. -/
def lhSumTopOf (π : P ⟶ X) (ξ : Hmod K P 2) (r : ℕ) :
    ((i : Fin (r + 1)) → Hmod K X (2 * r - 2 * (i : ℕ))) →ₗ[K] Hmod K P (2 * r) where
  toFun a := ∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i)
  map_add' a b := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => lhTerm_add π ξ (2 * r) (i : ℕ) (a i) (b i)
  map_smul' c a := by
    show ∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) ((c • a) i)
      = c • ∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => lhTerm_smulOf π ξ (2 * r) (i : ℕ) c (a i)

/-- **The coefficient product is the absolute top cohomology, over `K`.** -/
def lhTopEquivOf {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ} (L : LerayHirschGraded π ξ (r + 1)) :
    ((i : Fin (r + 1)) → Hmod K X (2 * r - 2 * (i : ℕ))) ≃ₗ[K] Hmod K P (2 * r) :=
  LinearEquiv.ofBijective (lhSumTopOf π ξ r) (LHCast.bijective_sum_lhTerm_topOf L)

/-! ## 2. The restriction square over `K` -/

/-- **The restriction of the pair, in Leray–Hirsch coordinates, over `K`.**  The first `r`
coefficients are carried across unchanged and the top one is folded into them by the Chern
relation on the subspace. -/
theorem absToSub_sum_lhTermOf (Z : Set P)
    (π : P ⟶ X) (π' : TopCat.of Z ⟶ X) (hπ : sInclusion Z ≫ π = π')
    (ξ : Hmod K P 2) (ξ' : Hmod K (TopCat.of Z) 2) (hξ : pull (sInclusion Z) 2 ξ = ξ')
    {r : ℕ} (L' : LerayHirschGraded π' ξ' r)
    (a : (i : Fin (r + 1)) → Hmod K X (2 * r - 2 * (i : ℕ))) :
    (absToSub K Z (2 * r)).hom
        (∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i))
      = ∑ i : Fin r, lhTerm π' ξ' (2 * r) (i : ℕ)
          (ThomDeg.restrictMap (R := K)
            (M := fun i : Fin (r + 1) => Hmod K X (2 * r - 2 * (i : ℕ)))
            (fun i => chernMulOf L' i) a i) := by
  have hterm : ∀ i : Fin (r + 1),
      pull (sInclusion Z) (2 * r) (lhTerm π ξ (2 * r) (i : ℕ) (a i))
        = lhTerm π' ξ' (2 * r) (i : ℕ) (a i) :=
    fun i => LHCast.pull_lhTermOf (sInclusion Z) π π' hπ ξ ξ' hξ (2 * r) (i : ℕ) (a i)
  have hlast : lhTerm π' ξ' (2 * r) ((Fin.last r : Fin (r + 1)) : ℕ) (a (Fin.last r))
      = ∑ i : Fin r, lhTerm π' ξ' (2 * r) (i : ℕ) (chernMulOf L' i (a (Fin.last r))) :=
    lhTerm_top_eq_sumOf L' (a (Fin.last r))
  show pull (sInclusion Z) (2 * r) (∑ i : Fin (r + 1), lhTerm π ξ (2 * r) (i : ℕ) (a i)) = _
  rw [pull_sum]
  simp only [hterm]
  rw [Fin.sum_univ_castSucc, hlast, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (lhTerm_add π' ξ' (2 * r) (i : ℕ) (a i.castSucc)
    (chernMulOf L' i (a (Fin.last r)))).symm

/-! ## 3. `habs` over `K` -/

/-- **From a commuting square with an injective bottom edge and one exactness, the range of
the coordinate map is a kernel**, over any commutative ring. -/
theorem range_comp_eq_ker_of_squareOf {A B C D E : Type}
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C] [AddCommGroup D] [Module K D]
    [AddCommGroup E] [Module K E]
    (Φ : A ≃ₗ[K] B) (j : C →ₗ[K] A) (ρ : A →ₗ[K] D)
    (T : B →ₗ[K] E) (Ψ : E → D) (hΨ0 : Ψ 0 = 0) (hΨ : Function.Injective Ψ)
    (hex : LinearMap.range j = LinearMap.ker ρ)
    (hsq : ∀ x : A, Ψ (T (Φ x)) = ρ x) :
    LinearMap.range (Φ.toLinearMap.comp j) = LinearMap.ker T := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    have hjc : ρ (j c) = 0 :=
      LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self j c)
    refine LinearMap.mem_ker.mpr (hΨ ?_)
    rw [hΨ0]
    exact (hsq (j c)).trans hjc
  · intro hy
    have hTy : T y = 0 := LinearMap.mem_ker.mp hy
    have hrho : ρ (Φ.symm y) = 0 := by
      rw [← hsq (Φ.symm y), Φ.apply_symm_apply, hTy, hΨ0]
    obtain ⟨c, hc⟩ : Φ.symm y ∈ LinearMap.range j := by
      rw [hex]; exact LinearMap.mem_ker.mpr hrho
    refine ⟨c, ?_⟩
    show Φ (j c) = y
    rw [hc, Φ.apply_symm_apply]

/-- **The coordinate image of the relative group is the kernel of the restriction**, over
`K`. -/
theorem range_thomJm_eq_ker_restrictMapOf (Z : Set P)
    (π : P ⟶ X) (π' : TopCat.of Z ⟶ X) (hπ : sInclusion Z ≫ π = π')
    (ξ : Hmod K P 2) (ξ' : Hmod K (TopCat.of Z) 2) (hξ : pull (sInclusion Z) 2 ξ = ξ')
    {r : ℕ} (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' r) :
    LinearMap.range (thomJmOf K (lhTopEquivOf L) Z)
      = LinearMap.ker (ThomDeg.restrictMap (R := K)
          (M := fun i : Fin (r + 1) => Hmod K X (2 * r - 2 * (i : ℕ)))
          (fun i => chernMulOf L' i)) := by
  have hΨinj : Function.Injective
      (fun b : (i : Fin r) → Hmod K X (2 * r - 2 * (i : ℕ)) =>
        ∑ i : Fin r, lhTerm π' ξ' (2 * r) (i : ℕ) (b i)) :=
    (LHCast.bijective_sum_lhTerm_of_gradedOf L' (2 * r) (lhDomainCard_two_mul r)).1
  refine range_comp_eq_ker_of_squareOf (lhTopEquivOf L).symm
    (relToAbs K P Z (2 * r)).hom (absToSub K Z (2 * r)).hom _
    (fun b => ∑ i : Fin r, lhTerm π' ξ' (2 * r) (i : ℕ) (b i)) ?_ hΨinj
    (range_relToAbs_eq_ker_absToSub K P Z (2 * r)) ?_
  · exact Finset.sum_eq_zero (fun i _ => lhTerm_zero π' ξ' (2 * r) (i : ℕ))
  · intro x
    have hx : ∑ i : Fin (r + 1),
        lhTerm π ξ (2 * r) (i : ℕ) ((lhTopEquivOf L).symm x i) = x :=
      (lhTopEquivOf L).apply_symm_apply x
    have hsq := absToSub_sum_lhTermOf Z π π' hπ ξ ξ' hξ L' ((lhTopEquivOf L).symm x)
    rw [hx] at hsq
    exact hsq.symm

/-! ## 4. The Thom data over `K` -/

/-- **`relToAbs` is injective at the top degree, over `K`.**  Exactness moves the question
one degree down, where the restriction is onto. -/
theorem relToAbs_injective_of_gradedOf (Z : Set P)
    (π : P ⟶ X) (π' : TopCat.of Z ⟶ X) (hπ : sInclusion Z ≫ π = π')
    (ξ : Hmod K P 2) (ξ' : Hmod K (TopCat.of Z) 2) (hξ : pull (sInclusion Z) 2 ξ = ξ')
    {r : ℕ} (hr : 1 ≤ r)
    (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' r) :
    Function.Injective (relToAbs K P Z (2 * r)).hom := by
  have hsurj : Function.Surjective (absToSub K Z (2 * r - 1)).hom :=
    LHCast.absToSub_surjective_of_gradedOf Z π π' hπ ξ ξ' hξ r hr L L'
  have hdeg : 2 * r - 1 + 1 = 2 * r := by omega
  rw [← hdeg]
  exact relToAbs_injective_of_absToSub_surjective K P Z (2 * r - 1) hsurj

/-- **The degreewise Thom data of the pair over `K`, from the two Leray–Hirsch instances.**
The `K`-form of `thomData_of_lerayHirsch`. -/
theorem thomData_of_lerayHirschOf (Z : Set P)
    (π : P ⟶ X) (π' : TopCat.of Z ⟶ X) (hπ : sInclusion Z ≫ π = π')
    (ξ : Hmod K P 2) (ξ' : Hmod K (TopCat.of Z) 2) (hξ : pull (sInclusion Z) 2 ξ = ξ')
    {r : ℕ} (hr : 1 ≤ r)
    (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' r) :
    ∃ (jm : ↥(relCohomology K P Z (2 * r)) →ₗ[K]
        ((i : Fin (r + 1)) → Hmod K X (2 * r - 2 * (i : ℕ))))
      (_ : Function.Injective jm),
      LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap (R := K)
        (M := fun i : Fin (r + 1) => Hmod K X (2 * r - 2 * (i : ℕ)))
        (fun i => chernMulOf L' i)) :=
  thomData_of_absToSubOf K (lhTopEquivOf L) Z
    (M := fun i : Fin (r + 1) => Hmod K X (2 * r - 2 * (i : ℕ)))
    (fun i => chernMulOf L' i) (LinearEquiv.refl K _)
    (relToAbs_injective_of_gradedOf Z π π' hπ ξ ξ' hξ hr L L')
    (range_thomJm_eq_ker_restrictMapOf Z π π' hπ ξ ξ' hξ L L')

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms absToSub_sum_lhTermOf
#audit_axioms range_thomJm_eq_ker_restrictMapOf
#audit_axioms thomData_of_lerayHirschOf

end ThomChernDeg

end

end GroupApproximation.CharClass
