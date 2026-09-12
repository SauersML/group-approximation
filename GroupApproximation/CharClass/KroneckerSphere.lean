import GroupApproximation.CharClass.KroneckerSphereHomology
import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.CharClass.CohomologyContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# The cohomology of a sphere, over any coefficient field

Step 4c of the universal-coefficient port (lane `lix-cupone`): the `K`-coefficient twin of
`CharClass/CohomologySphere.lean` and of the degree-zero half of
`CharClass/CohomologyContractible.lean`.

```text
Hᵏ(Sⁿ; K) = 0 for k ∉ {0, n},     Hⁿ(Sⁿ; K) ≃ₗ K (n ≥ 1),     H⁰(X; K) ≃ₗ K (X path connected).
```

Each statement is the homology statement of `KroneckerSphereHomology.lean` dualised through
`kroneckerEquivOf K X n : Hⁿ(X; K) ≅ Hom_K(Hₙ(X; K), K)`.  The top rank goes through
`Subspace.dual_finrank_eq`, which needs `[Field K]` and nothing else — it handles the
infinite-dimensional case itself, so no finiteness hypothesis is added.  This is the input
the odd side needs at odd `p`, where `K = ZMod p`.

Nothing vendored and no existing `CharClass` file is edited; §4 restates the `ZMod 2`
instances so a consumer can see that the generic statements specialise to the `F₂` ones.
-/

open CategoryTheory AlgebraicTopology Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

namespace GroupApproximation
namespace CharClass

/-! ## 1. Vanishing -/

/-- `Hᵏ(Sⁿ; K) = 0` for `k > n`. -/
theorem sphere_coh_isZero_of_gtOf (K : Type) [Field K] (n k : ℕ) (h : n < k) :
    IsZero (Hmod K (TopCat.of (Sphere n)) k) :=
  IsZero.of_iso
    (homologyDualOf_isZero_of_homology_isZero K (TopCat.of (Sphere n)) k
      (sphereHomologyOf_isZero_of_gt K n k h))
    (kroneckerEquivOf K (TopCat.of (Sphere n)) k)

/-- `Hᵏ(Sⁿ; K) = 0` for `0 < k < n`. -/
theorem sphere_coh_isZero_of_ltOf (K : Type) [Field K] (n k : ℕ) (h0 : 0 < k) (hkn : k < n) :
    IsZero (Hmod K (TopCat.of (Sphere n)) k) :=
  IsZero.of_iso
    (homologyDualOf_isZero_of_homology_isZero K (TopCat.of (Sphere n)) k
      (sphereHomologyOf_isZero_of_lt K n k h0 hkn))
    (kroneckerEquivOf K (TopCat.of (Sphere n)) k)

/-- `Hᵏ(Sⁿ; K) = 0` whenever `k` is neither `0` nor `n`. -/
theorem sphere_coh_isZero_of_neOf (K : Type) [Field K] (n k : ℕ) (h0 : k ≠ 0) (hkn : k ≠ n) :
    IsZero (Hmod K (TopCat.of (Sphere n)) k) :=
  IsZero.of_iso
    (homologyDualOf_isZero_of_homology_isZero K (TopCat.of (Sphere n)) k
      (sphereHomologyOf_isZero_of_ne K n k h0 hkn))
    (kroneckerEquivOf K (TopCat.of (Sphere n)) k)

/-- Every class of `Hᵏ(Sⁿ; K)` vanishes when `k ∉ {0, n}`. -/
theorem sphere_coh_eq_zero_of_neOf (K : Type) [Field K] (n k : ℕ) (h0 : k ≠ 0) (hkn : k ≠ n)
    (a : Hmod K (TopCat.of (Sphere n)) k) : a = 0 := by
  have h := sphere_coh_isZero_of_neOf K n k h0 hkn
  rw [ModuleCat.isZero_iff_subsingleton] at h
  exact h.elim a 0

/-! ## 2. The top degree -/

/-- **`Hⁿ(Sⁿ; K)` is one dimensional** for `n ≥ 1`. -/
theorem sphere_coh_top_finrankOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank K (Hmod K (TopCat.of (Sphere n)) n) = 1 := by
  have e : Hmod K (TopCat.of (Sphere n)) n ≃ₗ[K]
      (homologyOf K (TopCat.of (Sphere n)) n →ₗ[K] K) :=
    (kroneckerEquivOf K (TopCat.of (Sphere n)) n).toLinearEquiv
  rw [e.finrank_eq]
  exact Subspace.dual_finrank_eq.trans (sphereHomologyOf_top_finrank K n hn)

theorem sphere_coh_top_nontrivialOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    Nontrivial (Hmod K (TopCat.of (Sphere n)) n) :=
  Module.nontrivial_of_finrank_eq_succ (n := 0) (sphere_coh_top_finrankOf K n hn)

theorem sphere_coh_top_finiteOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    Module.Finite K (Hmod K (TopCat.of (Sphere n)) n) :=
  Module.finite_of_finrank_pos (by rw [sphere_coh_top_finrankOf K n hn]; exact Nat.one_pos)

/-- `Hⁿ(Sⁿ; K) ≃ₗ K` for `n ≥ 1`. -/
def sphereTopEquivOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    Hmod K (TopCat.of (Sphere n)) n ≃ₗ[K] K :=
  haveI := sphere_coh_top_finiteOf K n hn
  LinearEquiv.ofFinrankEq _ _ (by rw [sphere_coh_top_finrankOf K n hn]; simp)

/-- A nonzero class in `Hⁿ(Sⁿ; K)`, `n ≥ 1`: a fundamental class over `K`. -/
def sphereTopClassOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    Hmod K (TopCat.of (Sphere n)) n :=
  (sphereTopEquivOf K n hn).symm 1

theorem sphereTopClassOf_ne_zero (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    sphereTopClassOf K n hn ≠ 0 := by
  have h : (sphereTopEquivOf K n hn) (sphereTopClassOf K n hn) = 1 :=
    (sphereTopEquivOf K n hn).apply_symm_apply 1
  intro hz
  rw [hz, map_zero] at h
  exact one_ne_zero h.symm

/-- Every class of `Hⁿ(Sⁿ; K)` is a multiple of the top class. -/
theorem sphere_coh_top_eq_smulOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n)
    (a : Hmod K (TopCat.of (Sphere n)) n) :
    a = (sphereTopEquivOf K n hn a) • sphereTopClassOf K n hn := by
  rw [sphereTopClassOf, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]

/-! ## 3. Degree zero -/

/-- **`H⁰(X; K)` is one dimensional for a nonempty path-connected space**: the augmentation
is an isomorphism on `H₀`, and the universal coefficient isomorphism dualises it. -/
theorem cohZero_finrankOf (K : Type) [Field K] (X : TopCat.{0}) [Nonempty X]
    [PathConnectedSpace X] : Module.finrank K (Hmod K X 0) = 1 := by
  haveI : IsIso (H0Gen.H0aug K X) := H0Gen.isIso_H0aug (R := K) X
  have e : Hmod K X 0 ≃ₗ[K] (homologyOf K X 0 →ₗ[K] K) :=
    (kroneckerEquivOf K X 0).toLinearEquiv
  have e2 : homologyOf K X 0 ≃ₗ[K] K :=
    (asIso (H0Gen.H0aug K X)).toLinearEquiv
  rw [e.finrank_eq]
  refine Subspace.dual_finrank_eq.trans ?_
  rw [e2.finrank_eq]
  simp

theorem cohZero_finiteOf (K : Type) [Field K] (X : TopCat.{0}) [Nonempty X]
    [PathConnectedSpace X] : Module.Finite K (Hmod K X 0) :=
  Module.finite_of_finrank_pos (by rw [cohZero_finrankOf K X]; exact Nat.one_pos)

/-- `H⁰(X; K) ≃ₗ K` for a nonempty path-connected space. -/
def cohZeroEquivOf (K : Type) [Field K] (X : TopCat.{0}) [Nonempty X] [PathConnectedSpace X] :
    Hmod K X 0 ≃ₗ[K] K :=
  haveI := cohZero_finiteOf K X
  LinearEquiv.ofFinrankEq _ _ (by rw [cohZero_finrankOf K X]; simp)

/-- `H⁰(Sⁿ; K) ≃ₗ K` for `n ≥ 1`. -/
def sphereCohZeroEquivOf (K : Type) [Field K] (n : ℕ) (hn : 1 ≤ n) :
    Hmod K (TopCat.of (Sphere n)) 0 ≃ₗ[K] K :=
  haveI := sphere_nonempty n hn
  haveI := sphere_pathConnectedSpace n hn
  cohZeroEquivOf K (TopCat.of (Sphere n))

/-- **`H⁰(Y; K) ≃ₗ K` for a contractible `Y`.** -/
def cohZeroEquivOfContractibleOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y]
    [ContractibleSpace Y] : Hmod K (TopCat.of Y) 0 ≃ₗ[K] K :=
  haveI : Nonempty (TopCat.of Y) := nonempty_of_contractible Y
  haveI : PathConnectedSpace (TopCat.of Y) := inferInstanceAs (PathConnectedSpace Y)
  cohZeroEquivOf K (TopCat.of Y)

/-! ## 4. The `ZMod 2` instances are the statements of `CohomologySphere.lean` -/

theorem sphere_coh_isZero_of_neOf_zmod2 (n k : ℕ) (h0 : k ≠ 0) (hkn : k ≠ n) :
    IsZero (Hmod2 (TopCat.of (Sphere n)) k) :=
  sphere_coh_isZero_of_neOf (ZMod 2) n k h0 hkn

theorem sphere_coh_top_finrankOf_zmod2 (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank (ZMod 2) (Hmod2 (TopCat.of (Sphere n)) n) = 1 :=
  sphere_coh_top_finrankOf (ZMod 2) n hn

/-! ## 5. Closed endpoint -/

/-- The sphere computation in cohomology over every field: vanishing off `{0, n}`, a line
in the top degree, and a line in degree zero, for `n ≥ 1`. -/
def SphereCohomologyOverField : Prop :=
  (∀ (K : Type) [Field K] (n k : ℕ), k ≠ 0 → k ≠ n →
      IsZero (Hmod K (TopCat.of (Sphere n)) k)) ∧
    (∀ (K : Type) [Field K] (n : ℕ), 1 ≤ n →
      Module.finrank K (Hmod K (TopCat.of (Sphere n)) n) = 1) ∧
    ∀ (K : Type) [Field K] (n : ℕ), 1 ≤ n →
      Nonempty (Hmod K (TopCat.of (Sphere n)) 0 ≃ₗ[K] K)

theorem sphereCohomologyOverField : SphereCohomologyOverField :=
  ⟨fun K _ n k h0 hkn => sphere_coh_isZero_of_neOf K n k h0 hkn,
    fun K _ n hn => sphere_coh_top_finrankOf K n hn,
    fun K _ n hn => ⟨sphereCohZeroEquivOf K n hn⟩⟩

#audit_closed_axioms sphereCohomologyOverField

end CharClass
end GroupApproximation

end
