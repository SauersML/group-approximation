import GroupApproximation.Algebra.SchreierGenerators
import GroupApproximation.Algebra.HyperbolicQuasiIsometry

/-!
# A finite-index subgroup is quasi-isometric to the ambient group

`Kazhdan/SharpExistenceRoutes.lean` asserts, in prose, that
`Hyperbolic.HyperbolicFiniteIndexPermanence` "is an instance of
`Hyperbolic.QuasiIsometryInvariant`, since a finite-index subgroup is
quasi-isometric to the ambient group".  This module proves that assertion, so
that the reduction is machine-checked rather than asserted:

* `isQuasiIsometry_retractMap` --- the retraction `γ ↦ γ·sec(γ)⁻¹` of
  `Algebra/FiniteIndexTransversal.lean` is a quasi-isometry from `Γ` with a
  finite symmetric generating set `S` to `Λ` with the Schreier alphabet of
  `Algebra/SchreierGenerators.lean`;
* `isHyperbolicGroup_subgroup_of_quasiIsometryInvariant` --- so hyperbolicity
  passes to finite-index subgroups as soon as it is a quasi-isometry invariant.

The constants are explicit and are exactly the two comparisons of
`Algebra/SchreierGenerators.lean`: the multiplicative one is the largest ambient
length of a Schreier generator, and the additive one is twice the largest
ambient length of a coset representative --- the distance from a point to its
retraction.

**What this does not do.**  It does not prove hyperbolicity is a
quasi-isometry invariant; `Algebra/HyperbolicQuasiIsometry.lean` records that
statement as open, and the Morse lemma is what it needs.  What is settled here
is that the finite-index question is not a *second* open problem.
-/

namespace GroupApproximation
namespace FiniteIndex

open WordMetric Hyperbolic

universe u

variable {Γ : Type u} [Group Γ] {Λ : Subgroup Γ}

/-- The retraction of `Algebra/FiniteIndexTransversal.lean`, valued in the
subgroup. -/
def retractMap (tr : RightTransversal Γ Λ) (γ : Γ) : ↥Λ :=
  ⟨tr.retract γ, tr.retract_mem γ⟩

variable (tr : RightTransversal Γ Λ)

@[simp] theorem retractMap_coe (γ : Γ) : (retractMap tr γ : Γ) = tr.retract γ := rfl

/-- The retraction restricts to the identity on the subgroup, so it is
surjective. -/
@[simp] theorem retractMap_of_mem (a : ↥Λ) : retractMap tr (a : Γ) = a :=
  Subtype.ext (tr.retract_of_mem a.2)

/-- The distance from a point to its retraction is the ambient length of its
coset representative. -/
theorem wordDist_retractMap_self {S : Set Γ} (hS : IsSymmetricGeneratingSet S) (γ : Γ) :
    wordDist S γ (tr.retract γ) = wordNorm S (tr.sec γ) := by
  show wordNorm S (γ⁻¹ * (γ * (tr.sec γ)⁻¹)) = wordNorm S (tr.sec γ)
  rw [inv_mul_cancel_left, wordNorm_inv hS]

/-- ... and the same on the other side. -/
theorem wordDist_self_retractMap {S : Set Γ} (hS : IsSymmetricGeneratingSet S) (γ : Γ) :
    wordDist S (tr.retract γ) γ = wordNorm S (tr.sec γ) := by
  rw [wordDist_comm hS, wordDist_retractMap_self tr hS]

/-- **The retraction onto a finite-index subgroup is a quasi-isometry.**

The Lipschitz direction has multiplicative constant `1` --- one ambient step is
one Schreier step --- and the constants only enter the coarse-inverse direction:
`M` is the largest ambient length of a Schreier generator and `D` the largest
ambient length of a coset representative. -/
theorem isQuasiIsometry_retractMap {S : Set Γ} (hS : IsSymmetricGeneratingSet S)
    (hSfin : S.Finite) :
    ∃ K C : ℕ, IsQuasiIsometry S (schreierSet tr S) (retractMap tr) K C := by
  classical
  obtain ⟨M, hM⟩ := exists_wordNorm_le_mul_schreier tr hS (schreierSet_finite tr hSfin)
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ∀ c ∈ tr.reps, wordNorm S c ≤ D :=
    ⟨tr.reps.sup fun c => wordNorm S c, fun c hc => Finset.le_sup hc⟩
  refine ⟨max 1 M, 2 * D, ⟨?_, ?_⟩⟩
  · intro x y
    constructor
    · -- one ambient step moves the retraction by one Schreier step
      have h₁ : wordDist (schreierSet tr S) (retractMap tr x) (retractMap tr y)
          ≤ wordDist S x y := wordDist_retract_le tr hS x y
      have h₂ : wordDist S x y ≤ max 1 M * wordDist S x y :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    · -- and back, at the price of the two comparison constants
      have hsecx : wordNorm S (tr.sec x) ≤ D := hD _ (tr.sec_mem_reps x)
      have hsecy : wordNorm S (tr.sec y) ≤ D := hD _ (tr.sec_mem_reps y)
      have hx : wordDist S x (tr.retract x) ≤ D := by
        rw [wordDist_retractMap_self tr hS]; exact hsecx
      have hy : wordDist S (tr.retract y) y ≤ D := by
        rw [wordDist_self_retractMap tr hS]; exact hsecy
      have hmid : wordDist S (tr.retract x) (tr.retract y)
          ≤ M * wordDist (schreierSet tr S) (retractMap tr x) (retractMap tr y) := by
        have h := hM ((retractMap tr x)⁻¹ * retractMap tr y)
        simpa [wordDist] using h
      have htri₁ : wordDist S x y ≤ wordDist S x (tr.retract x)
          + wordDist S (tr.retract x) y := wordDist_triangle hS _ _ _
      have htri₂ : wordDist S (tr.retract x) y ≤ wordDist S (tr.retract x) (tr.retract y)
          + wordDist S (tr.retract y) y := wordDist_triangle hS _ _ _
      have hmax : M * wordDist (schreierSet tr S) (retractMap tr x) (retractMap tr y)
          ≤ max 1 M * wordDist (schreierSet tr S) (retractMap tr x) (retractMap tr y) :=
        Nat.mul_le_mul_right _ (le_max_right 1 M)
      omega
  · intro b
    exact ⟨(b : Γ), by simp [wordDist_self]⟩

/-- **Hyperbolicity passes to finite-index subgroups as soon as it is a
quasi-isometry invariant.**  The generating set produced downstairs is the
Schreier alphabet, which is finite because the index is. -/
theorem isHyperbolicGroup_subgroup_of_quasiIsometryInvariant
    (h : QuasiIsometryInvariant) {G : Type} [Group G] (Λ : Subgroup G) [Λ.FiniteIndex]
    (hG : IsHyperbolicGroup G) : IsHyperbolicGroup ↥Λ := by
  classical
  obtain ⟨S, hS, δ, h4⟩ := hG
  obtain ⟨tr⟩ := exists_rightTransversal Λ
  have hSfin : (S : Set G).Finite := S.finite_toSet
  have hTfin : (schreierSet tr (S : Set G)).Finite := schreierSet_finite tr hSfin
  have hT : IsSymmetricGeneratingSet (schreierSet tr (S : Set G)) :=
    isSymmetricGeneratingSet_schreierSet tr hS
  obtain ⟨K, C, hqi⟩ := isQuasiIsometry_retractMap tr hS hSfin
  obtain ⟨δ', h4'⟩ :=
    h G ↥Λ inferInstance inferInstance (S : Set G) (schreierSet tr (S : Set G))
      (retractMap tr) K C hS hT hqi ⟨δ, h4⟩
  refine ⟨hTfin.toFinset, ?_, δ', ?_⟩
  · rw [hTfin.coe_toFinset]; exact hT
  · rw [hTfin.coe_toFinset]; exact h4'

end FiniteIndex
end GroupApproximation
