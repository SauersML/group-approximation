import GroupApproximation.CharClass.CohomologyMayerVietoris

/-!
# Covers of a product, and the vanishing form of Mayer–Vietoris

The Künneth computations of the LIX program all have the same shape: a space `Y`
is covered by two opens whose cohomology is known, and one wants the cohomology
of `A × Y` from that of `A` and of the pieces.  This file supplies the plumbing.

* `prodOpen A U` is the open `A × U` of `A × Y` attached to an open `U` of `Y`,
  with `prodSubtypeHomeo` identifying it with `A × ↥U`;
* `isZero_mvAmbient` is Mayer–Vietoris in the only form the recursions use:
  vanishing on the intersection in degree `m` and on both pieces in degree `m+1`
  forces vanishing on the whole space in degree `m+1`;
* `isZero_cohomology_of_isEmpty` handles the empty intersection, which is what a
  cover by two *disjoint* opens produces.

## Main declarations

* `isZero_of_linearEquiv`, `isZero_mvAmbient`.
* `prodOpen`, `prodOpen_sup`, `prodOpen_coe_inter`, `prodSubtypeHomeo`.
* `isZero_prodOpen_of_contractible` — `A × U` has the vanishing of `A` when `U` is
  contractible.
* `isEmpty_singularSimplices`, `isZero_cohomology_of_isEmpty`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. Transport of vanishing -/

/-- Vanishing transports along a linear equivalence. -/
theorem isZero_of_linearEquiv {M N : ModuleCat.{0} (ZMod 2)} (e : M ≃ₗ[ZMod 2] N)
    (h : IsZero M) : IsZero N := by
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  haveI := h
  exact e.toEquiv.symm.subsingleton

/-! ## 2. Mayer–Vietoris in vanishing form -/

/-- **Mayer–Vietoris, vanishing form.**  If `H^m(U ∩ V; F₂) = 0` and both
`H^{m+1}(U; F₂)` and `H^{m+1}(V; F₂)` vanish, then `H^{m+1}(Z; F₂) = 0`.  This is
the only consequence of the long exact sequence that the punctured-product and
Künneth recursions use. -/
theorem isZero_mvAmbient {Z : TopCat.{0}} (U V : Opens Z) (hUV : U ⊔ V = ⊤) (m : ℕ)
    (hI : IsZero (Hmod2 (TopCat.of ↥((U : Set Z) ∩ (V : Set Z))) m))
    (hU : IsZero (Hmod2 (TopCat.of (U : Set Z)) (m + 1)))
    (hV : IsZero (Hmod2 (TopCat.of (V : Set Z)) (m + 1))) :
    IsZero (Hmod2 Z (m + 1)) := by
  have h1 : IsZero ((mvCoSC U V hUV).X₃.homology m) :=
    IsZero.of_iso hI (mvInterIso U V hUV m)
  have h2 : IsZero ((mvCoSC U V hUV).X₂.homology (m + 1)) :=
    isZero_mvCoX2 U V hUV (m + 1) hU hV
  have hz : IsZero ((mvCoSC U V hUV).X₁.homology (m + 1)) :=
    (mvExact_ambient U V hUV m).isZero_X₂ (h1.eq_of_src _ _) (h2.eq_of_tgt _ _)
  exact IsZero.of_iso hz (mvAmbientIso U V hUV (m + 1)).symm

/-! ## 3. Opens of a product -/

/-- The open `A × U` of `A × Y` attached to an open `U` of `Y`. -/
def prodOpen (A : Type) [TopologicalSpace A] {Y : Type} [TopologicalSpace Y] (U : Opens Y) :
    Opens (A × Y) where
  carrier := Prod.snd ⁻¹' (U : Set Y)
  is_open' := U.isOpen.preimage continuous_snd

@[simp] theorem prodOpen_coe (A : Type) [TopologicalSpace A] {Y : Type} [TopologicalSpace Y]
    (U : Opens Y) : ((prodOpen A U : Opens (A × Y)) : Set (A × Y)) = Prod.snd ⁻¹' (U : Set Y) :=
  rfl

theorem prodOpen_sup (A : Type) [TopologicalSpace A] {Y : Type} [TopologicalSpace Y]
    {U V : Opens Y} (h : U ⊔ V = ⊤) : prodOpen A U ⊔ prodOpen A V = ⊤ := by
  apply Opens.ext
  have hset : (U : Set Y) ∪ (V : Set Y) = Set.univ := by
    have h' := congrArg (fun W : Opens Y => (W : Set Y)) h
    simpa using h'
  show (Prod.snd ⁻¹' (U : Set Y)) ∪ (Prod.snd ⁻¹' (V : Set Y)) = Set.univ
  rw [← Set.preimage_union, hset, Set.preimage_univ]

theorem prodOpen_coe_inter (A : Type) [TopologicalSpace A] {Y : Type} [TopologicalSpace Y]
    (U V : Opens Y) :
    ((prodOpen A U : Set (A × Y)) ∩ (prodOpen A V : Set (A × Y)))
      = Prod.snd ⁻¹' ((U : Set Y) ∩ (V : Set Y)) := by
  rw [prodOpen_coe, prodOpen_coe, ← Set.preimage_inter]

/-- `A × S` inside `A × Y`, for a subset `S ⊆ Y`, is homeomorphic to `A × ↥S`. -/
def prodSubtypeHomeo (A : Type) [TopologicalSpace A] {Y : Type} [TopologicalSpace Y]
    (S : Set Y) : ↥(Prod.snd ⁻¹' S : Set (A × Y)) ≃ₜ A × ↥S where
  toEquiv :=
    { toFun := fun p => (p.1.1, ⟨p.1.2, p.2⟩)
      invFun := fun q => ⟨(q.1, q.2.1), q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The cohomology of the open `A × U` is that of `A × ↥U`. -/
def prodOpenCohEquiv (A : Type) [TopologicalSpace A] {Y : Type} [TopologicalSpace Y]
    (U : Opens Y) (k : ℕ) :
    Hmod2 (TopCat.of (A × ↥(U : Set Y))) k
      ≃ₗ[ZMod 2] Hmod2 (TopCat.of ↥((prodOpen A U : Opens (A × Y)) : Set (A × Y))) k :=
  pullEquivOfHomeomorph (prodSubtypeHomeo A (U : Set Y)) k

/-- **`A × U` inherits the vanishing of `A` when `U` is contractible.** -/
theorem isZero_prodOpen_of_contractible (A : Type) [TopologicalSpace A] {Y : Type}
    [TopologicalSpace Y] (U : Opens Y) [ContractibleSpace ↥(U : Set Y)] (k : ℕ)
    (h : IsZero (Hmod2 (TopCat.of A) k)) :
    IsZero (Hmod2 (TopCat.of ↥((prodOpen A U : Opens (A × Y)) : Set (A × Y))) k) :=
  isZero_of_linearEquiv (prodOpenCohEquiv A U k)
    (isZero_of_linearEquiv (cohProdContractible A ↥(U : Set Y) k) h)

/-! ## 4. The empty space -/

/-- A space with no points has no singular simplices: a singular simplex is a
continuous map out of the standard simplex, which is nonempty. -/
theorem isEmpty_singularSimplices (Y : TopCat.{0}) [IsEmpty Y] (n : ℕ) :
    IsEmpty (singularSimplices Y n) := by
  constructor
  intro τ
  exact IsEmpty.false
    ((TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk n)) τ)
      ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩)

/-- All cochains on a space with no points agree. -/
theorem subsingleton_cochainGroup_of_isEmpty (Y : TopCat.{0}) [IsEmpty Y] (n : ℕ) :
    Subsingleton (singularCochainGroup (ZMod 2) Y n) := by
  haveI := isEmpty_singularSimplices Y n
  exact ⟨fun φ ψ => cochain_ext (fun τ => (IsEmpty.false τ).elim)⟩

/-- **`H^k(∅; F₂) = 0` in every degree.** -/
theorem isZero_cohomology_of_isEmpty (Y : Type) [TopologicalSpace Y] [IsEmpty Y] (k : ℕ) :
    IsZero (Hmod2 (TopCat.of Y) k) := by
  haveI : IsEmpty (TopCat.of Y) := inferInstanceAs (IsEmpty Y)
  haveI := subsingleton_cochainGroup_of_isEmpty (TopCat.of Y) k
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro a b
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycle a
  obtain ⟨ψ, hψ, rfl⟩ := exists_cocycle b
  exact cocycleClass_congr (TopCat.of Y) k (Subsingleton.elim φ ψ) hφ hψ

end

end GroupApproximation.CharClass
