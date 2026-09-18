import GroupApproximation.Analysis.KKTheoryKasparov

/-!
# Homotopy classes of non-unital `⋆`-homomorphisms

Cuntz's picture of Kasparov theory (J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987)
31--51) presents `KK(A, B)` as homotopy classes of `⋆`-homomorphisms between
*non-unital* C⋆-algebras (the stabilized algebras `𝒦 ⊗ qA`), with the Kasparov product
realized by composition.  This file sets up the purely formal layer of that picture:

* `NHomotopic f g`: a pointwise continuous path of non-unital `⋆`-homomorphisms from `f` to
  `g` (the non-unital analogue of `KK.Homotopic`);
* its stability under composition on either side;
* `HomotopyClass A B`: the quotient of `A →⋆ₙₐ[ℂ] B` by homotopy, with composition,
  identities, associativity and unit laws.

Manuscript: `non_mf_group_notes.tex`, the UCT hypothesis of Tikuisis--White--Winter
(`thm:fixed-radical-membership`); this is infrastructure for the concrete Kasparov theory
`kasparovKK` of lane TWWKK.
-/

namespace GroupApproximation.Full.TWWKK

universe u v w x

noncomputable section

/-- **Homotopy of non-unital `⋆`-homomorphisms**: a pointwise norm-continuous path joining `f`
to `g`. -/
def NHomotopic {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    (f g : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∃ p : ℝ → (A →⋆ₙₐ[ℂ] B),
    (∀ a : A, Continuous fun t : ℝ => p t a) ∧ p 0 = f ∧ p 1 = g

section Homotopy

variable {A : Type u} {B : Type v} {C : Type w}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

theorem NHomotopic.refl (f : A →⋆ₙₐ[ℂ] B) : NHomotopic f f :=
  ⟨fun _ => f, fun _ => continuous_const, rfl, rfl⟩

theorem NHomotopic.symm {f g : A →⋆ₙₐ[ℂ] B} (h : NHomotopic f g) : NHomotopic g f := by
  obtain ⟨p, hp, h0, h1⟩ := h
  refine ⟨fun t => p (1 - t),
    fun a => (hp a).comp (continuous_const.sub continuous_id), ?_, ?_⟩
  · show p (1 - 0) = g
    rw [sub_zero]; exact h1
  · show p (1 - 1) = f
    rw [sub_self]; exact h0

/-- A `⋆`-homomorphism between C⋆-algebras is continuous (it is contractive). -/
theorem continuous_nonUnitalStarAlgHom (k : B →⋆ₙₐ[ℂ] C) : Continuous fun b : B => k b :=
  AddMonoidHomClass.continuous_of_bound k 1 fun b => by
    rw [one_mul]
    exact NonUnitalStarAlgHom.norm_apply_le k b

/-- Precomposition preserves homotopy. -/
theorem NHomotopic.comp_right {f g : B →⋆ₙₐ[ℂ] C} (h : NHomotopic f g)
    (k : A →⋆ₙₐ[ℂ] B) : NHomotopic (f.comp k) (g.comp k) := by
  obtain ⟨p, hp, h0, h1⟩ := h
  refine ⟨fun t => (p t).comp k, fun a => hp (k a), ?_, ?_⟩
  · show (p 0).comp k = f.comp k
    rw [h0]
  · show (p 1).comp k = g.comp k
    rw [h1]

/-- Postcomposition preserves homotopy; this uses the continuity of `⋆`-homomorphisms. -/
theorem NHomotopic.comp_left (k : B →⋆ₙₐ[ℂ] C) {f g : A →⋆ₙₐ[ℂ] B}
    (h : NHomotopic f g) : NHomotopic (k.comp f) (k.comp g) := by
  obtain ⟨p, hp, h0, h1⟩ := h
  refine ⟨fun t => k.comp (p t), fun a => (continuous_nonUnitalStarAlgHom k).comp (hp a),
    ?_, ?_⟩
  · show k.comp (p 0) = k.comp f
    rw [h0]
  · show k.comp (p 1) = k.comp g
    rw [h1]

end Homotopy

/-- A homotopy of unital `⋆`-homomorphisms (`KK.Homotopic`) is a homotopy of the underlying
non-unital `⋆`-homomorphisms. -/
theorem nHomotopic_of_homotopic {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    {f g : A →⋆ₐ[ℂ] B} (h : KK.Homotopic f g) :
    NHomotopic f.toNonUnitalStarAlgHom g.toNonUnitalStarAlgHom := by
  obtain ⟨p, hp, h0, h1⟩ := h
  refine ⟨fun t => (p t).toNonUnitalStarAlgHom, fun a => hp a, ?_, ?_⟩
  · show (p 0).toNonUnitalStarAlgHom = f.toNonUnitalStarAlgHom
    rw [h0]
  · show (p 1).toNonUnitalStarAlgHom = g.toNonUnitalStarAlgHom
    rw [h1]

/-! ## Homotopy classes -/

/-- **Homotopy classes** of non-unital `⋆`-homomorphisms `A → B`. -/
def HomotopyClass (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] : Type (max u v) :=
  Quot (@NHomotopic A B _ _)

namespace HomotopyClass

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}
variable [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [NonUnitalCStarAlgebra D]

/-- The class of a `⋆`-homomorphism. -/
def mk (f : A →⋆ₙₐ[ℂ] B) : HomotopyClass A B :=
  Quot.mk _ f

theorem mk_eq_mk_of_nHomotopic {f g : A →⋆ₙₐ[ℂ] B} (h : NHomotopic f g) : mk f = mk g :=
  Quot.sound h

/-- Induction principle for homotopy classes (used as the eliminator in `induction`). -/
@[elab_as_elim]
theorem ind {motive : HomotopyClass A B → Prop}
    (mk : ∀ f : A →⋆ₙₐ[ℂ] B, motive (HomotopyClass.mk f)) (x : HomotopyClass A B) :
    motive x :=
  Quot.ind (β := motive) mk x

/-- **Composition** of homotopy classes: `comp y x` is "first `x`, then `y`". -/
def comp (y : HomotopyClass B C) (x : HomotopyClass A B) : HomotopyClass A C :=
  Quot.lift
    (fun g : B →⋆ₙₐ[ℂ] C =>
      Quot.lift (fun f : A →⋆ₙₐ[ℂ] B => mk (g.comp f))
        (fun _ _ h => mk_eq_mk_of_nHomotopic (h.comp_left g)) x)
    (fun _ _ h => by
      induction x using HomotopyClass.ind with
      | mk f => exact mk_eq_mk_of_nHomotopic (h.comp_right f))
    y

theorem comp_mk (g : B →⋆ₙₐ[ℂ] C) (f : A →⋆ₙₐ[ℂ] B) :
    comp (mk g) (mk f) = mk (g.comp f) :=
  rfl

/-- The identity class. -/
def id (A : Type u) [NonUnitalCStarAlgebra A] : HomotopyClass A A :=
  mk (NonUnitalStarAlgHom.id ℂ A)

theorem comp_assoc (z : HomotopyClass C D) (y : HomotopyClass B C) (x : HomotopyClass A B) :
    comp (comp z y) x = comp z (comp y x) := by
  induction x using HomotopyClass.ind with
  | mk f =>
    induction y using HomotopyClass.ind with
    | mk g =>
      induction z using HomotopyClass.ind with
      | mk k =>
        show mk ((k.comp g).comp f) = mk (k.comp (g.comp f))
        rw [NonUnitalStarAlgHom.comp_assoc]

theorem id_comp (x : HomotopyClass A B) : comp (id B) x = x := by
  induction x using HomotopyClass.ind with
  | mk f =>
    show mk ((NonUnitalStarAlgHom.id ℂ B).comp f) = mk f
    rw [NonUnitalStarAlgHom.id_comp]

theorem comp_id (x : HomotopyClass A B) : comp x (id A) = x := by
  induction x using HomotopyClass.ind with
  | mk f =>
    show mk (f.comp (NonUnitalStarAlgHom.id ℂ A)) = mk f
    rw [NonUnitalStarAlgHom.comp_id]

end HomotopyClass

end

end GroupApproximation.Full.TWWKK
