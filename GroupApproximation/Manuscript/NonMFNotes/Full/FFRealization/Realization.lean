import GroupApproximation.Manuscript.NonMFNotes.Full.FFRealization.Presented
import GroupApproximation.Sofic.RealizationFromUniversalGroup

/-!
# `rem:ff-realization`: the realization at the printed datum `P₁ × P₂ × S ≤ P`

Manuscript `non_mf_group_notes.tex`, Remark `rem:ff-realization`:

> The construction of [FFF, §2] gives a finitely presented torsion-free
> property-(T) group `P` containing `P₁ × P₂ × S`, where `Pᵢ ≅ P` and `S` is
> finitely presented, simple, and torsion-free.  Choose an isomorphism
> `α : P → P₁` and `a ∈ P₂ ∖ {1}`.  Define `E(P,α,a)` ...  Thus `w ≠ 1`, and
> `E(P,α,a)` has torsion.

The printed direct product `P₁ × P₂ × S ≤ P` is carried as an injective
homomorphism `P × P × S →* P` (`ProductDatum`).  The printed "isomorphism
`α : P → P₁`" is an injective endomorphism of `P` whose image is `P₁`
(`remFFRealization`), and every genuine isomorphism `P ≃* P₁` gives one
(`alphaOfEquiv`, `remFFRealization_of_equiv`).  From this datum alone ---
no property of `P` or `S` is used --- `a ∉ α(P)` follows (`P₁ ∩ P₂ = 1`), so
the file `Presented.lean` applies: `w ≠ 1`, `w² = 1`, `w` central,
`E(P,α,a)` has torsion, and, because `P` has property (T), `E(P,α,a)` is not
MF.  `S` plays no role in the remark's conclusions and none of its printed
properties (finite presentation, simplicity, torsion-freeness) is assumed.

The datum is linked to the existing `ContainsSquare` API
(`ProductDatum.toContainsSquare`).

**What is not proved here.**  The remark's first sentence --- that some
finitely presented torsion-free property-(T) group `P` admits such a datum ---
is the theorem of [FFF, §2] (built from Chiodo's universal finitely presented
torsion-free group, Kotowski--Ollivier random quotients and Osin's small
cancellation theory).  It is not formalized in this development, and nothing
in this file asserts it or takes a hypothesis standing in for it: `P`, `hT` and
the datum are the printed quantified objects of the remark, and every theorem
below holds for all of them.
-/

namespace GroupApproximation.Full.NN08

noncomputable section

universe w

/-- **The printed direct product `P₁ × P₂ × S ≤ P`** (`rem:ff-realization`),
recorded as an injective homomorphism `P × P × S →* P`. -/
structure ProductDatum (P S : Type) [Group P] [Group S] where
  /-- The embedding of `P × P × S`, whose image is the printed
  `P₁ × P₂ × S ≤ P`. -/
  emb : (P × P × S) →* P
  /-- Injectivity: the image really is a copy of `P × P × S`. -/
  emb_injective : Function.Injective emb

namespace ProductDatum

variable {P S : Type} [Group P] [Group S] (D : ProductDatum P S)

/-- The first factor inclusion `P → P₁ ≤ P`. -/
def factorOne : P →* P := D.emb.comp (MonoidHom.inl P (P × S))

/-- The second factor inclusion `P → P₂ ≤ P`. -/
def factorTwo : P →* P :=
  D.emb.comp ((MonoidHom.inr P (P × S)).comp (MonoidHom.inl P S))

theorem factorOne_apply (p : P) : D.factorOne p = D.emb (p, 1) := rfl

theorem factorTwo_apply (b : P) : D.factorTwo b = D.emb (1, b, 1) := rfl

/-- `P₁ ≅ P`. -/
theorem factorOne_injective : Function.Injective D.factorOne := by
  intro x y hxy
  rw [D.factorOne_apply x, D.factorOne_apply y] at hxy
  exact congrArg Prod.fst (D.emb_injective hxy)

/-- `P₂ ≅ P`. -/
theorem factorTwo_injective : Function.Injective D.factorTwo := by
  intro x y hxy
  rw [D.factorTwo_apply x, D.factorTwo_apply y] at hxy
  exact congrArg (fun z : P × P × S => z.2.1) (D.emb_injective hxy)

/-- **`a ∈ P₂ ∖ {1}` lies outside the image of `α`**, for any `α` with image
`P₁`: the two factors of the direct product meet trivially. -/
theorem not_mem_range_of_range_eq {α : P →* P}
    (hrange : α.range = D.factorOne.range) {a : P}
    (haP₂ : a ∈ D.factorTwo.range) (ha : a ≠ 1) : a ∉ Set.range α := by
  rintro ⟨p, hp⟩
  have hp₁ : α p ∈ D.factorOne.range := by
    rw [← hrange]
    exact MonoidHom.mem_range.mpr ⟨p, rfl⟩
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hp₁
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp haP₂
  have hemb : D.emb (g, 1) = D.emb (1, b, 1) :=
    calc D.emb (g, 1) = D.factorOne g := rfl
      _ = α p := hg
      _ = a := hp
      _ = D.factorTwo b := hb.symm
      _ = D.emb (1, b, 1) := rfl
  have hb1 : b = 1 :=
    congrArg (fun z : P × P × S => z.2.1) (D.emb_injective hemb).symm
  apply ha
  rw [← hb, hb1, map_one]

/-- The printed "isomorphism `α : P → P₁`", as an endomorphism of `P`. -/
def alphaOfEquiv (e : P ≃* D.factorOne.range) : P →* P :=
  D.factorOne.range.subtype.comp e.toMonoidHom

theorem alphaOfEquiv_injective (e : P ≃* D.factorOne.range) :
    Function.Injective (D.alphaOfEquiv e) := by
  intro x y hxy
  have hxy' :
      ((e x : D.factorOne.range) : P) = ((e y : D.factorOne.range) : P) :=
    hxy
  exact e.injective (Subtype.val_injective hxy')

theorem alphaOfEquiv_range (e : P ≃* D.factorOne.range) :
    (D.alphaOfEquiv e).range = D.factorOne.range := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hx
    exact (e p).2
  · intro hx
    refine MonoidHom.mem_range.mpr ⟨e.symm ⟨x, hx⟩, ?_⟩
    exact congrArg Subtype.val (MulEquiv.apply_symm_apply e ⟨x, hx⟩)

/-- The first two factors form a `ContainsSquare` datum, so the existing
`RealizationFromUniversalGroup` API applies. -/
def toContainsSquare : RealizationFromUniversalGroup.ContainsSquare P where
  emb := D.emb.comp (MonoidHom.prodMap (MonoidHom.id P) (MonoidHom.inl P S))
  emb_injective := by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    have hxy' : D.emb (x₁, x₂, 1) = D.emb (y₁, y₂, 1) := hxy
    have h := D.emb_injective hxy'
    have h₁ : x₁ = y₁ := congrArg Prod.fst h
    have h₂ : x₂ = y₂ := congrArg (fun z : P × P × S => z.2.1) h
    rw [h₁, h₂]

theorem toContainsSquare_alpha : D.toContainsSquare.alpha = D.factorOne :=
  MonoidHom.ext fun _ => rfl

theorem toContainsSquare_emb_second (b : P) :
    D.toContainsSquare.emb (1, b) = D.factorTwo b := rfl

end ProductDatum

/-- **`rem:ff-realization`, at the printed datum.**  Let `P` be finitely
presented with property (T), let `P₁ × P₂ × S ≤ P` be a direct product with
`P₁, P₂ ≅ P`, let `α : P → P` be injective with image `P₁`, and let
`a ∈ P₂ ∖ {1}`.  Then `E(P,α,a)` is finitely presented, `P` embeds in it, the
central word `w` is a nontrivial involution (so `E(P,α,a)` has torsion), and
`E(P,α,a)` is not MF. -/
theorem remFFRealization {P S : Type} [Group P] [Group S]
    [Group.IsFinitelyPresented P]
    (hT : HasKazhdanPropertyTComplex.{0, w} P) (D : ProductDatum P S)
    {α : P →* P} (hα : Function.Injective α)
    (hrange : α.range = D.factorOne.range)
    {a : P} (haP₂ : a ∈ D.factorTwo.range) (ha : a ≠ 1) :
    Group.IsFinitelyPresented (EPα P α a) ∧
      Function.Injective (EPα.base α a) ∧
      EPα.w α a ≠ 1 ∧
      EPα.w α a ^ 2 = 1 ∧
      (∀ g : EPα P α a, Commute (EPα.w α a) g) ∧
      ¬ IsPowerTorsionFree (EPα P α a) ∧
      ¬ IsOperatorMF (EPα P α a) ∧
      ¬ IsCDEOperatorMF (EPα P α a) := by
  have haα : a ∉ Set.range α := D.not_mem_range_of_range_eq hrange haP₂ ha
  exact ⟨ePα_finitelyPresented α a, ePα_base_injective hα haα,
    ePα_mark_ne_one hα haα, ePα_w_sq α a, ePα_w_central α a,
    ePα_not_isPowerTorsionFree hα haα,
    ePα_not_isOperatorMF (hasKazhdanPropertyT_iff_textbook.mpr hT) hα haα,
    ePα_not_isCDEOperatorMF hT hα haα⟩

/-- `rem:ff-realization` with `α` given literally as an isomorphism
`P ≃* P₁`: the printed conclusions `w ≠ 1` and "`E(P,α,a)` has torsion".
These need no property (T). -/
theorem remFFRealization_of_equiv {P S : Type} [Group P] [Group S]
    [Group.IsFinitelyPresented P] (D : ProductDatum P S)
    (e : P ≃* D.factorOne.range)
    {a : P} (haP₂ : a ∈ D.factorTwo.range) (ha : a ≠ 1) :
    EPα.w (D.alphaOfEquiv e) a ≠ 1 ∧
      ∃ x : EPα P (D.alphaOfEquiv e) a, x ≠ 1 ∧ x ^ 2 = 1 := by
  have haα : a ∉ Set.range (D.alphaOfEquiv e) :=
    D.not_mem_range_of_range_eq (D.alphaOfEquiv_range e) haP₂ ha
  have hne : EPα.w (D.alphaOfEquiv e) a ≠ 1 :=
    ePα_mark_ne_one (D.alphaOfEquiv_injective e) haα
  exact ⟨hne, EPα.w (D.alphaOfEquiv e) a, hne, ePα_w_sq _ a⟩

/-- **`rem:ff-realization` as one closed proposition**: all printed data are
quantified inside. -/
def FFRealizationStatement : Prop :=
  ∀ {P S : Type} [Group P] [Group S] [Group.IsFinitelyPresented P]
    (hT : HasKazhdanPropertyTComplex.{0, w} P) (D : ProductDatum P S)
    (α : P →* P) (hα : Function.Injective α)
    (hrange : α.range = D.factorOne.range)
    (a : P) (haP₂ : a ∈ D.factorTwo.range) (ha : a ≠ 1),
    Group.IsFinitelyPresented (EPα P α a) ∧
      Function.Injective (EPα.base α a) ∧
      EPα.w α a ≠ 1 ∧
      EPα.w α a ^ 2 = 1 ∧
      (∀ g : EPα P α a, Commute (EPα.w α a) g) ∧
      ¬ IsPowerTorsionFree (EPα P α a) ∧
      ¬ IsOperatorMF (EPα P α a) ∧
      ¬ IsCDEOperatorMF (EPα P α a)

/-- **`rem:ff-realization`** (closed endpoint). -/
theorem ffRealization : FFRealizationStatement.{w} := by
  intro P S _ _ _ hT D α hα hrange a haP₂ ha
  exact remFFRealization hT D hα hrange haP₂ ha

#audit_axioms GroupApproximation.Full.NN08.ProductDatum.not_mem_range_of_range_eq
#audit_axioms GroupApproximation.Full.NN08.remFFRealization
#audit_axioms GroupApproximation.Full.NN08.remFFRealization_of_equiv
#audit_closed_axioms GroupApproximation.Full.NN08.ffRealization

end

end GroupApproximation.Full.NN08
