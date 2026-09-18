import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.NonUnitalHomotopy

/-!
# `⋆`-homomorphisms out of `ℂ` are projections

The first ingredient of `K₀(ℂ) = ℤ` in Cuntz's picture of Kasparov theory (J. Cuntz, *A new look
at KK-theory*, K-Theory 1 (1987), §2; Blackadar, *K-Theory for Operator Algebras*, 17.3):
a non-unital `⋆`-homomorphism `ℂ → B` is the same thing as a star projection of `B`, namely its
value at `1`, and a homotopy of such homomorphisms is the same thing as a norm-continuous path of
projections.

* `complexHom p hp : ℂ →⋆ₙₐ[ℂ] B`, `z ↦ z • p`;
* `complexHomEquiv : (ℂ →⋆ₙₐ[ℂ] B) ≃ {p : B // IsStarProjection p}`;
* `ProjectionPath p q`: a continuous path of star projections from `p` to `q`;
* `nHomotopic_iff_projectionPath : NHomotopic φ ψ ↔ ProjectionPath (φ 1) (ψ 1)`;
* orthogonal sums: `complexHom_add`, and postcomposition `comp_complexHom`.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-Complex, work order WO-TWWKK-C: `stabQ.Hom ℂ ℂ ≃+ ℤ`).
-/

namespace GroupApproximation.Full.TWWKK

universe u v

noncomputable section

section Projection

variable {B : Type u} [NonUnitalCStarAlgebra B]

/-- **The `⋆`-homomorphism of a projection**: `z ↦ z • p`. -/
def complexHom (p : B) (hp : IsStarProjection p) : ℂ →⋆ₙₐ[ℂ] B where
  toFun z := z • p
  map_smul' c z := by
    show (c * z) • p = c • (z • p)
    rw [smul_smul]
  map_zero' := zero_smul ℂ p
  map_add' z w := add_smul z w p
  map_mul' z w := by
    show (z * w) • p = (z • p) * (w • p)
    rw [smul_mul_smul_comm, hp.isIdempotentElem.eq]
  map_star' z := by
    show star z • p = star (z • p)
    rw [star_smul, hp.isSelfAdjoint.star_eq]

theorem complexHom_apply (p : B) (hp : IsStarProjection p) (z : ℂ) :
    complexHom p hp z = z • p :=
  rfl

theorem complexHom_apply_one (p : B) (hp : IsStarProjection p) :
    complexHom p hp 1 = p :=
  one_smul ℂ p

/-- The value at `1` of a `⋆`-homomorphism out of `ℂ` is a star projection. -/
theorem isStarProjection_apply_one (φ : ℂ →⋆ₙₐ[ℂ] B) : IsStarProjection (φ 1) := by
  refine ⟨?_, ?_⟩
  · show φ 1 * φ 1 = φ 1
    rw [← map_mul, one_mul]
  · show star (φ 1) = φ 1
    rw [← map_star, star_one]

/-- A `⋆`-homomorphism out of `ℂ` is determined by its value at `1`. -/
theorem apply_eq_smul_apply_one (φ : ℂ →⋆ₙₐ[ℂ] B) (z : ℂ) : φ z = z • φ 1 := by
  calc φ z = φ (z • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
    _ = z • φ 1 := map_smul φ z (1 : ℂ)

theorem complexHom_apply_one_eq (φ : ℂ →⋆ₙₐ[ℂ] B) :
    complexHom (φ 1) (isStarProjection_apply_one φ) = φ :=
  NonUnitalStarAlgHom.ext fun z => by
    show z • φ 1 = φ z
    rw [apply_eq_smul_apply_one φ z]

/-- Two `⋆`-homomorphisms out of `ℂ` agreeing at `1` are equal. -/
theorem complexHom_ext {φ ψ : ℂ →⋆ₙₐ[ℂ] B} (h : φ 1 = ψ 1) : φ = ψ :=
  NonUnitalStarAlgHom.ext fun z => by
    rw [apply_eq_smul_apply_one φ z, apply_eq_smul_apply_one ψ z, h]

/-- **`⋆`-homomorphisms `ℂ → B` are the star projections of `B`.** -/
def complexHomEquiv : (ℂ →⋆ₙₐ[ℂ] B) ≃ {p : B // IsStarProjection p} where
  toFun φ := ⟨φ 1, isStarProjection_apply_one φ⟩
  invFun p := complexHom p.1 p.2
  left_inv φ := complexHom_apply_one_eq φ
  right_inv p := Subtype.ext (complexHom_apply_one p.1 p.2)

theorem complexHomEquiv_apply (φ : ℂ →⋆ₙₐ[ℂ] B) : (complexHomEquiv φ : B) = φ 1 :=
  rfl

/-- Postcomposition of the homomorphism of a projection. -/
theorem comp_complexHom {C : Type v} [NonUnitalCStarAlgebra C] (k : B →⋆ₙₐ[ℂ] C)
    (p : B) (hp : IsStarProjection p) :
    k.comp (complexHom p hp) = complexHom (k p) (hp.map k) :=
  complexHom_ext (by
    show k ((1 : ℂ) • p) = (1 : ℂ) • k p
    rw [one_smul, one_smul])

/-- The homomorphism of an orthogonal sum of projections is the pointwise sum. -/
theorem complexHom_add (p q : B) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : p * q = 0) (z : ℂ) :
    complexHom (p + q) (hp.add hq hpq) z = complexHom p hp z + complexHom q hq z :=
  smul_add z p q

/-! ## Homotopies are paths of projections -/

/-- A norm-continuous path of star projections from `p` to `q`. -/
def ProjectionPath (p q : B) : Prop :=
  ∃ P : ℝ → B, Continuous P ∧ (∀ t, IsStarProjection (P t)) ∧ P 0 = p ∧ P 1 = q

theorem ProjectionPath.refl {p : B} (hp : IsStarProjection p) : ProjectionPath p p :=
  ⟨fun _ => p, continuous_const, fun _ => hp, rfl, rfl⟩

theorem ProjectionPath.symm {p q : B} (h : ProjectionPath p q) : ProjectionPath q p := by
  obtain ⟨P, hP, hproj, h0, h1⟩ := h
  refine ⟨fun t => P (1 - t), hP.comp (continuous_const.sub continuous_id),
    fun t => hproj (1 - t), ?_, ?_⟩
  · show P (1 - 0) = q
    rw [sub_zero]; exact h1
  · show P (1 - 1) = p
    rw [sub_self]; exact h0

/-- The endpoints of a projection path are projections. -/
theorem ProjectionPath.isStarProjection_left {p q : B} (h : ProjectionPath p q) :
    IsStarProjection p := by
  obtain ⟨P, _, hproj, h0, _⟩ := h
  rw [← h0]; exact hproj 0

theorem ProjectionPath.isStarProjection_right {p q : B} (h : ProjectionPath p q) :
    IsStarProjection q := by
  obtain ⟨P, _, hproj, _, h1⟩ := h
  rw [← h1]; exact hproj 1

/-- A projection path is carried along by a `⋆`-homomorphism. -/
theorem ProjectionPath.map {C : Type v} [NonUnitalCStarAlgebra C] (k : B →⋆ₙₐ[ℂ] C)
    {p q : B} (h : ProjectionPath p q) : ProjectionPath (k p) (k q) := by
  obtain ⟨P, hP, hproj, h0, h1⟩ := h
  refine ⟨fun t => k (P t), (continuous_nonUnitalStarAlgHom k).comp hP,
    fun t => (hproj t).map k, ?_, ?_⟩
  · show k (P 0) = k p
    rw [h0]
  · show k (P 1) = k q
    rw [h1]

/-- **Homotopy of homomorphisms out of `ℂ` is homotopy of projections.** -/
theorem nHomotopic_iff_projectionPath (φ ψ : ℂ →⋆ₙₐ[ℂ] B) :
    NHomotopic φ ψ ↔ ProjectionPath (φ 1) (ψ 1) := by
  constructor
  · rintro ⟨p, hp, h0, h1⟩
    refine ⟨fun t => p t 1, hp 1, fun t => isStarProjection_apply_one (p t), ?_, ?_⟩
    · show p 0 1 = φ 1
      rw [h0]
    · show p 1 1 = ψ 1
      rw [h1]
  · rintro ⟨P, hP, hproj, h0, h1⟩
    refine ⟨fun t => complexHom (P t) (hproj t), fun z => ?_, ?_, ?_⟩
    · show Continuous fun t => z • P t
      exact hP.const_smul z
    · show complexHom (P 0) (hproj 0) = φ
      exact complexHom_ext (by rw [complexHom_apply_one, h0])
    · show complexHom (P 1) (hproj 1) = ψ
      exact complexHom_ext (by rw [complexHom_apply_one, h1])

theorem nHomotopic_complexHom_iff (p q : B) (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    NHomotopic (complexHom p hp) (complexHom q hq) ↔ ProjectionPath p q := by
  rw [nHomotopic_iff_projectionPath, complexHom_apply_one, complexHom_apply_one]

/-- Homotopy classes of homomorphisms `ℂ → B`, from a projection. -/
def projectionClass (p : B) (hp : IsStarProjection p) : HomotopyClass ℂ B :=
  HomotopyClass.mk (complexHom p hp)

theorem projectionClass_eq_of_path {p q : B} (h : ProjectionPath p q) :
    projectionClass p h.isStarProjection_left = projectionClass q h.isStarProjection_right :=
  HomotopyClass.mk_eq_mk_of_nHomotopic ((nHomotopic_complexHom_iff p q _ _).mpr h)

/-- Every homotopy class of homomorphisms out of `ℂ` is the class of a projection. -/
theorem exists_projectionClass_eq (x : HomotopyClass ℂ B) :
    ∃ (p : B) (hp : IsStarProjection p), projectionClass p hp = x := by
  induction x using HomotopyClass.ind with
  | mk φ =>
    exact ⟨φ 1, isStarProjection_apply_one φ, by
      show HomotopyClass.mk (complexHom (φ 1) _) = HomotopyClass.mk φ
      rw [complexHom_apply_one_eq]⟩

end Projection

end

end GroupApproximation.Full.TWWKK
