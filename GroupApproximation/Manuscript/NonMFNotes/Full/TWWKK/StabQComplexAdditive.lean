import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabQComplexRank
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabQGroupAbstract

/-!
# The Cuntz sum adds ranks

The third ingredient of `K₀(ℂ) = ℤ` in Cuntz's picture of Kasparov theory (J. Cuntz, *A new
look at KK-theory*, K-Theory 1 (1987), §2--3; Blackadar, *K-Theory for Operator Algebras*, 17.3):
a rank function on the projections of a stable algebra, constant along projection paths and
additive on orthogonal projections, turns the Cuntz sum of homotopy classes into addition.

* `ProjectionRank E`: a natural-number valued function on `E` which is constant along
  projection paths and additive on orthogonal star projections;
* `ProjectionRank.classRank : HomotopyClass ℂ E → ℕ`, the rank of the image of `1`;
* `ProjectionRank.classRank_addClass`: for a Cuntz-stable `E`, the Cuntz sum adds ranks;
* `ProjectionRank.homRank e`: the rank of the image of a fixed projection `e` (for `D = 𝒦`
  and `e` a rank-one projection this indexes `[𝒦, 𝒦]`), with `homRank_addClass`;
* `matrixRank n`: the matrix rank on `M_n(ℂ)` is a `ProjectionRank`.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-Complex, work order WO-TWWKK-C: `stabQ.Hom ℂ ℂ ≃+ ℤ`).
-/

open scoped ComplexOrder

namespace GroupApproximation.Full.TWWKK

universe u v

noncomputable section

/-- A **rank on projections**: natural-number valued, constant along projection paths and
additive on orthogonal star projections. -/
structure ProjectionRank (E : Type v) [NonUnitalCStarAlgebra E] where
  /-- The rank function. -/
  toFun : E → ℕ
  /-- The rank is constant along projection paths. -/
  path_eq : ∀ {p q : E}, ProjectionPath p q → toFun p = toFun q
  /-- The rank is additive on orthogonal star projections. -/
  add_eq : ∀ {p q : E}, IsStarProjection p → IsStarProjection q → p * q = 0 →
    toFun (p + q) = toFun p + toFun q

namespace ProjectionRank

variable {D : Type u} {E : Type v} [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E]
variable (R : ProjectionRank E)

/-- The zero projection has rank zero. -/
theorem toFun_zero : R.toFun 0 = 0 := by
  have h := R.add_eq (IsStarProjection.zero E) (IsStarProjection.zero E) (mul_zero (0 : E))
  rw [add_zero] at h
  omega

/-- **The rank of a homotopy class** of `⋆`-homomorphisms `ℂ → E`: the rank of the image of
`1`. -/
def classRank (x : HomotopyClass ℂ E) : ℕ :=
  Quot.lift (fun φ : ℂ →⋆ₙₐ[ℂ] E => R.toFun (φ 1))
    (fun φ ψ h => R.path_eq ((nHomotopic_iff_projectionPath φ ψ).mp h)) x

theorem classRank_mk (φ : ℂ →⋆ₙₐ[ℂ] E) :
    R.classRank (HomotopyClass.mk φ) = R.toFun (φ 1) :=
  rfl

theorem classRank_projectionClass (p : E) (hp : IsStarProjection p) :
    R.classRank (projectionClass p hp) = R.toFun p := by
  show R.toFun (complexHom p hp 1) = R.toFun p
  rw [complexHom_apply_one]

/-- The zero class has rank zero. -/
theorem classRank_zero : R.classRank (HomotopyClass.mk (0 : ℂ →⋆ₙₐ[ℂ] E)) = 0 := by
  show R.toFun ((0 : ℂ →⋆ₙₐ[ℂ] E) 1) = 0
  rw [NonUnitalStarAlgHom.zero_apply]
  exact R.toFun_zero

/-- The rank of an orthogonal sum of homomorphisms out of `ℂ` is the sum of the ranks. -/
theorem classRank_orthSum (u u' : ℂ →⋆ₙₐ[ℂ] E) (h : NOrth u u') :
    R.classRank (HomotopyClass.mk (orthSum u u' h)) =
      R.classRank (HomotopyClass.mk u) + R.classRank (HomotopyClass.mk u') := by
  show R.toFun (u 1 + u' 1) = R.toFun (u 1) + R.toFun (u' 1)
  exact R.add_eq (isStarProjection_apply_one u) (isStarProjection_apply_one u') (h 1 1).1

/-- The first Cuntz isometry does not change the rank. -/
theorem toFun_ι₁ (S : CuntzStable E) (φ : ℂ →⋆ₙₐ[ℂ] E) :
    R.toFun (S.ι₁ (φ 1)) = R.toFun (φ 1) :=
  R.path_eq ((nHomotopic_iff_projectionPath (S.ι₁.comp φ) φ).mp (S.nHomotopic_ι₁_comp φ))

/-- The second Cuntz isometry does not change the rank. -/
theorem toFun_ι₂ (S : CuntzStable E) (φ : ℂ →⋆ₙₐ[ℂ] E) :
    R.toFun (S.ι₂ (φ 1)) = R.toFun (φ 1) := by
  have h : R.toFun (S.ι₁ (φ 1)) = R.toFun (S.ι₂ (φ 1)) :=
    R.path_eq ((nHomotopic_iff_projectionPath (S.ι₁.comp φ) (S.ι₂.comp φ)).mp
      (S.nHomotopic_ι₁_ι₂_comp φ))
  exact h.symm.trans (R.toFun_ι₁ S φ)

/-- **The Cuntz sum adds ranks.** -/
theorem classRank_addClass (S : CuntzStable E) (x y : HomotopyClass ℂ E) :
    R.classRank (S.addClass x y) = R.classRank x + R.classRank y := by
  induction x using HomotopyClass.ind with
  | mk f =>
    induction y using HomotopyClass.ind with
    | mk g =>
      show R.toFun (S.ι₁ (f 1) + S.ι₂ (g 1)) = R.toFun (f 1) + R.toFun (g 1)
      rw [R.add_eq ((isStarProjection_apply_one f).map S.ι₁)
        ((isStarProjection_apply_one g).map S.ι₂) (S.orth (f 1) (g 1)).1,
        R.toFun_ι₁ S f, R.toFun_ι₂ S g]

/-! ## The rank of the image of a projection -/

/-- **The rank of a homotopy class `[D, E]` at a projection `e` of `D`**: the rank of the image
of `e`.  For `D = E = 𝒦` and `e` a rank-one projection this is the invariant indexing
`[𝒦, 𝒦]`. -/
def homRank (e : D) (he : IsStarProjection e) (x : HomotopyClass D E) : ℕ :=
  R.classRank (HomotopyClass.comp x (projectionClass e he))

theorem homRank_mk (e : D) (he : IsStarProjection e) (f : D →⋆ₙₐ[ℂ] E) :
    R.homRank e he (HomotopyClass.mk f) = R.toFun (f e) := by
  show R.toFun (f ((1 : ℂ) • e)) = R.toFun (f e)
  rw [one_smul]

/-- The zero class has rank zero at every projection. -/
theorem homRank_zero (e : D) (he : IsStarProjection e) :
    R.homRank e he (HomotopyClass.mk (0 : D →⋆ₙₐ[ℂ] E)) = 0 := by
  show R.toFun ((0 : D →⋆ₙₐ[ℂ] E) (complexHom e he 1)) = 0
  rw [NonUnitalStarAlgHom.zero_apply]
  exact R.toFun_zero

/-- **The Cuntz sum adds the ranks of the images of a projection.** -/
theorem homRank_addClass (S : CuntzStable E) (e : D) (he : IsStarProjection e)
    (x y : HomotopyClass D E) :
    R.homRank e he (S.addClass x y) = R.homRank e he x + R.homRank e he y := by
  show R.classRank (HomotopyClass.comp (S.addClass x y) (projectionClass e he)) =
    R.classRank (HomotopyClass.comp x (projectionClass e he)) +
      R.classRank (HomotopyClass.comp y (projectionClass e he))
  rw [S.comp_addClass_right]
  exact R.classRank_addClass S _ _

end ProjectionRank

/-! ## The matrix rank -/

/-- **The matrix rank on `M_n(ℂ)`** is a rank on projections. -/
def matrixRank (n : ℕ) : ProjectionRank (CStarMatrix (Fin n) (Fin n) ℂ) where
  toFun := projectionRank
  path_eq h := h.projectionRank_eq
  add_eq hp hq hpq := projectionRank_add hp hq hpq

theorem matrixRank_toFun (n : ℕ) (p : CStarMatrix (Fin n) (Fin n) ℂ) :
    (matrixRank n).toFun p = projectionRank p :=
  rfl

theorem classRank_matrixRank (n : ℕ) (x : HomotopyClass ℂ (CStarMatrix (Fin n) (Fin n) ℂ)) :
    (matrixRank n).classRank x = homotopyClassRank x :=
  rfl

end

end GroupApproximation.Full.TWWKK
