import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabQGroupOrth

/-!
# The Cuntz sum on homotopy classes: abelian group and bilinear composition

Let `D, E` be C⋆-algebras carrying `CuntzStable` structures (stable algebras, e.g. `𝒦 ⊗ X`).
This file proves the formal core of Cuntz's theorem (J. Cuntz, *A new look at KK-theory*,
K-Theory 1 (1987), §1--3; Blackadar, *K-Theory for Operator Algebras*, 17.8).

* The Cuntz sum descends to `HomotopyClass D E` (`CuntzStable.addClass`).  It is associative and
  commutative, and `[0]` is its unit.  The key step is `mk_orthSum`: an orthogonal sum is homotopic
  to the Cuntz sum.  It uses the rotation path `ι₁ ⤳ ι₂`.
* Precomposition is additive (`comp_addClass_right`, formal).
* **Postcomposition by an arbitrary `⋆`-homomorphism is additive** (`comp_addClass_left`).
  `y ∘ (x ⊕ x') = y ι₁ x + y ι₂ x'` is an orthogonal sum, hence homotopic to
  `(y ι₁ x) ⊕ (y ι₂ x') ≃ (y x) ⊕ (y x')`.
* Given an endomorphism `ν` of `D` with `[id ⊕ ν] = 0`, the classes form an abelian group, and
  `-[x] = [x ∘ ν]` (`cuntzAddCommGroup`).  For `D = 𝒦 ⊗ qA`, `ν = 𝒦 ⊗ flip` (the q-trick).
* `mk_sum_id_eq_zero`: `[id ⊕ ν] = 0` follows from a matrix rotation, i.e. an orthogonal pair
  `w₁ ⊥ w₂ : D → W` with `w₁ + w₂ ≃ 0` and a combination map `Φ : W → D`,
  `Φ w₁ = ι₁`, `Φ w₂ = ι₂ ν`.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`.
Work order `WO-TWWKK-B`.
-/

namespace GroupApproximation.Full.TWWKK

universe u v w

noncomputable section

namespace CuntzStable

variable {D : Type u} {E : Type v} {E' : Type w} {D' : Type*}
variable [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra E']
  [NonUnitalCStarAlgebra D']
variable (S : CuntzStable E)

theorem mk_ι₁_comp (x : D →⋆ₙₐ[ℂ] E) : HomotopyClass.mk (S.ι₁.comp x) = HomotopyClass.mk x :=
  HomotopyClass.mk_eq_mk_of_nHomotopic (S.nHomotopic_ι₁_comp x)

theorem mk_ι₂_comp (x : D →⋆ₙₐ[ℂ] E) : HomotopyClass.mk (S.ι₂.comp x) = HomotopyClass.mk x :=
  (HomotopyClass.mk_eq_mk_of_nHomotopic (S.nHomotopic_ι₁_ι₂_comp x)).symm.trans (S.mk_ι₁_comp x)

/-- **An orthogonal sum is homotopic to the Cuntz sum.** -/
theorem mk_orthSum (u u' : D →⋆ₙₐ[ℂ] E) (h : NOrth u u') :
    HomotopyClass.mk (orthSum u u' h) = HomotopyClass.mk (S.sum u u') := by
  have h₁ : HomotopyClass.mk (orthSum u u' h) =
      HomotopyClass.mk (S.ι₁.comp (orthSum u u' h)) :=
    (S.mk_ι₁_comp _).symm
  have hrot : ∀ t : ℝ, NOrth (S.ι₁.comp u) ((S.rot t).comp u') := fun t d d' =>
    ⟨S.rot_orth_left t (u d) (u' d') (h d d').1, S.rot_orth_right t (u d) (u' d') (h d d').2⟩
  have h₂ : NHomotopic (S.ι₁.comp (orthSum u u' h)) (S.sum u u') := by
    refine ⟨fun t => orthSum (S.ι₁.comp u) ((S.rot t).comp u') (hrot t), fun d => ?_, ?_, ?_⟩
    · show Continuous fun t : ℝ => S.ι₁ (u d) + S.rot t (u' d)
      exact continuous_const.add (S.rot_continuous (u' d))
    · refine NonUnitalStarAlgHom.ext fun d => ?_
      show S.ι₁ (u d) + S.rot 0 (u' d) = S.ι₁ (u d + u' d)
      rw [S.rot_zero, map_add]
    · refine NonUnitalStarAlgHom.ext fun d => ?_
      show S.ι₁ (u d) + S.rot 1 (u' d) = S.ι₁ (u d) + S.ι₂ (u' d)
      rw [S.rot_one]
  exact h₁.trans (HomotopyClass.mk_eq_mk_of_nHomotopic h₂)

/-- **The Cuntz sum of homotopy classes.** -/
def addClass (x y : HomotopyClass D E) : HomotopyClass D E :=
  Quot.lift
    (fun f : D →⋆ₙₐ[ℂ] E =>
      Quot.lift (fun g : D →⋆ₙₐ[ℂ] E => HomotopyClass.mk (S.sum f g))
        (fun _ _ h => HomotopyClass.mk_eq_mk_of_nHomotopic (S.sum_nHomotopic_right f h)) y)
    (fun _ _ h => by
      induction y using HomotopyClass.ind with
      | mk g => exact HomotopyClass.mk_eq_mk_of_nHomotopic (S.sum_nHomotopic_left h g))
    x

theorem addClass_mk (f g : D →⋆ₙₐ[ℂ] E) :
    S.addClass (HomotopyClass.mk f) (HomotopyClass.mk g) = HomotopyClass.mk (S.sum f g) :=
  rfl

theorem addClass_zero (x : HomotopyClass D E) :
    S.addClass x (HomotopyClass.mk (0 : D →⋆ₙₐ[ℂ] E)) = x := by
  induction x using HomotopyClass.ind with
  | mk f =>
    show HomotopyClass.mk (S.sum f 0) = HomotopyClass.mk f
    rw [S.sum_zero]
    exact S.mk_ι₁_comp f

theorem zero_addClass (x : HomotopyClass D E) :
    S.addClass (HomotopyClass.mk (0 : D →⋆ₙₐ[ℂ] E)) x = x := by
  induction x using HomotopyClass.ind with
  | mk f =>
    show HomotopyClass.mk (S.sum 0 f) = HomotopyClass.mk f
    rw [S.zero_sum]
    exact S.mk_ι₂_comp f

theorem addClass_comm (x y : HomotopyClass D E) : S.addClass x y = S.addClass y x := by
  induction x using HomotopyClass.ind with
  | mk f =>
    induction y using HomotopyClass.ind with
    | mk g =>
      show HomotopyClass.mk (S.sum f g) = HomotopyClass.mk (S.sum g f)
      calc HomotopyClass.mk (S.sum f g)
          = HomotopyClass.mk (orthSum (S.ι₂.comp g) (S.ι₁.comp f) (S.sum_orth f g).symm) :=
            congrArg HomotopyClass.mk (orthSum_comm (S.ι₁.comp f) (S.ι₂.comp g) (S.sum_orth f g))
        _ = HomotopyClass.mk (S.sum (S.ι₂.comp g) (S.ι₁.comp f)) := S.mk_orthSum _ _ _
        _ = S.addClass (HomotopyClass.mk (S.ι₂.comp g)) (HomotopyClass.mk (S.ι₁.comp f)) := rfl
        _ = S.addClass (HomotopyClass.mk g) (HomotopyClass.mk f) := by
            rw [S.mk_ι₂_comp g, S.mk_ι₁_comp f]
        _ = HomotopyClass.mk (S.sum g f) := rfl

theorem addClass_assoc (x y z : HomotopyClass D E) :
    S.addClass (S.addClass x y) z = S.addClass x (S.addClass y z) := by
  induction x using HomotopyClass.ind with
  | mk f =>
    induction y using HomotopyClass.ind with
    | mk g =>
      induction z using HomotopyClass.ind with
      | mk k =>
        show HomotopyClass.mk (S.sum (S.sum f g) k) = HomotopyClass.mk (S.sum f (S.sum g k))
        have hab : NOrth (S.ι₁.comp (S.ι₁.comp f)) (S.ι₁.comp (S.ι₂.comp g)) :=
          (S.sum_orth f g).comp_left S.ι₁
        have hac : NOrth (S.ι₁.comp (S.ι₁.comp f)) (S.ι₂.comp k) := S.sum_orth _ _
        have hbc : NOrth (S.ι₁.comp (S.ι₂.comp g)) (S.ι₂.comp k) := S.sum_orth _ _
        have e₁ : S.sum (S.sum f g) k =
            orthSum (S.ι₁.comp (S.ι₁.comp f))
              (orthSum (S.ι₁.comp (S.ι₂.comp g)) (S.ι₂.comp k) hbc)
              (NOrth.orthSum_right hbc hab hac) :=
          NonUnitalStarAlgHom.ext fun d => by
            show S.ι₁ (S.ι₁ (f d) + S.ι₂ (g d)) + S.ι₂ (k d) =
              S.ι₁ (S.ι₁ (f d)) + (S.ι₁ (S.ι₂ (g d)) + S.ι₂ (k d))
            rw [map_add, add_assoc]
        calc HomotopyClass.mk (S.sum (S.sum f g) k)
            = HomotopyClass.mk (S.sum (S.ι₁.comp (S.ι₁.comp f))
                (orthSum (S.ι₁.comp (S.ι₂.comp g)) (S.ι₂.comp k) hbc)) :=
              (congrArg HomotopyClass.mk e₁).trans (S.mk_orthSum _ _ _)
          _ = S.addClass (HomotopyClass.mk (S.ι₁.comp (S.ι₁.comp f)))
                (HomotopyClass.mk (orthSum (S.ι₁.comp (S.ι₂.comp g)) (S.ι₂.comp k) hbc)) :=
              rfl
          _ = S.addClass (HomotopyClass.mk f)
                (HomotopyClass.mk (S.sum (S.ι₁.comp (S.ι₂.comp g)) (S.ι₂.comp k))) := by
              rw [S.mk_orthSum (S.ι₁.comp (S.ι₂.comp g)) (S.ι₂.comp k) hbc,
                S.mk_ι₁_comp (S.ι₁.comp f), S.mk_ι₁_comp f]
          _ = S.addClass (HomotopyClass.mk f)
                (S.addClass (HomotopyClass.mk (S.ι₁.comp (S.ι₂.comp g)))
                  (HomotopyClass.mk (S.ι₂.comp k))) :=
              rfl
          _ = S.addClass (HomotopyClass.mk f)
                (S.addClass (HomotopyClass.mk g) (HomotopyClass.mk k)) := by
              rw [S.mk_ι₁_comp (S.ι₂.comp g), S.mk_ι₂_comp g, S.mk_ι₂_comp k]
          _ = HomotopyClass.mk (S.sum f (S.sum g k)) := rfl

/-- Precomposition is additive. -/
theorem comp_addClass_right (x x' : HomotopyClass D E) (z : HomotopyClass D' D) :
    HomotopyClass.comp (S.addClass x x') z =
      S.addClass (HomotopyClass.comp x z) (HomotopyClass.comp x' z) := by
  induction x using HomotopyClass.ind with
  | mk f =>
    induction x' using HomotopyClass.ind with
    | mk g =>
      induction z using HomotopyClass.ind with
      | mk h =>
        show HomotopyClass.mk ((S.sum f g).comp h) = HomotopyClass.mk (S.sum (f.comp h) (g.comp h))
        rw [S.sum_comp]

/-- **Postcomposition by an arbitrary class is additive.** -/
theorem comp_addClass_left (S' : CuntzStable E') (y : HomotopyClass E E')
    (x x' : HomotopyClass D E) :
    HomotopyClass.comp y (S.addClass x x') =
      S'.addClass (HomotopyClass.comp y x) (HomotopyClass.comp y x') := by
  induction x using HomotopyClass.ind with
  | mk f =>
    induction x' using HomotopyClass.ind with
    | mk g =>
      induction y using HomotopyClass.ind with
      | mk k =>
        show HomotopyClass.mk (k.comp (S.sum f g)) =
          S'.addClass (HomotopyClass.mk (k.comp f)) (HomotopyClass.mk (k.comp g))
        have hk₁ : HomotopyClass.mk (k.comp (S.ι₁.comp f)) = HomotopyClass.mk (k.comp f) :=
          congrArg (HomotopyClass.comp (HomotopyClass.mk k)) (S.mk_ι₁_comp f)
        have hk₂ : HomotopyClass.mk (k.comp (S.ι₂.comp g)) = HomotopyClass.mk (k.comp g) :=
          congrArg (HomotopyClass.comp (HomotopyClass.mk k)) (S.mk_ι₂_comp g)
        calc HomotopyClass.mk (k.comp (S.sum f g))
            = HomotopyClass.mk (S'.sum (k.comp (S.ι₁.comp f)) (k.comp (S.ι₂.comp g))) :=
              (congrArg HomotopyClass.mk (comp_orthSum k _ _ (S.sum_orth f g))).trans
                (S'.mk_orthSum _ _ _)
          _ = S'.addClass (HomotopyClass.mk (k.comp (S.ι₁.comp f)))
                (HomotopyClass.mk (k.comp (S.ι₂.comp g))) := rfl
          _ = S'.addClass (HomotopyClass.mk (k.comp f)) (HomotopyClass.mk (k.comp g)) := by
              rw [hk₁, hk₂]

end CuntzStable

end

end GroupApproximation.Full.TWWKK
