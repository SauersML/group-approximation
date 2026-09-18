import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZero.Dichotomy
import Mathlib.Algebra.Exact.Basic
import Mathlib.Logic.Relation

/-!
# The absorption criterion for `K₀ = 0` is sharp

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Q2). Work order WO-LVLowK-1.

`Absorb.lean` shows that over a ring `R` with a binary Leavitt family, `K₀(R) = 0` holds if every
f.g. projective module `P` satisfies `P ⊕ R ≅ R`. This file proves the converse, so the criterion
is an equivalence (`algKZero_trivial_iff_forall_absorbsRegular`).

* `absorbsRegular_of_prod_linearEquiv`: if `Q ⊕ P ≅ Q` for some f.g. projective `Q`, then `P`
  absorbs `R`. The proof writes `R ≅ K ⊕ Q` using the retraction `R → Q`
  (`exists_retraction_regular`) and computes `P ⊕ R ≅ K ⊕ (Q ⊕ P) ≅ K ⊕ Q ≅ R`.
* `absorbsRegular_of_cls_eq_zero`: `[P] = 0` in the Grothendieck group gives a stable
  isomorphism `Q ⊕ P ≅ Q ⊕ 0`, so `P` absorbs `R`.
-/

namespace GroupApproximation.Full.LVLowKZero

open GroupApproximation.Full.LVLowK

universe u v w

variable {R : Type u} [Ring R]

/-- **Cancelling a projective summand.** Over a ring with a binary Leavitt family, if
`Q ⊕ P ≅ Q` for a f.g. projective `Q`, then `P ⊕ R ≅ R`. -/
theorem absorbsRegular_of_prod_linearEquiv (L : LeavittFamily R) {P : Type v} {Q : Type w}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    [Module.Projective R Q] (e : (Q × P) ≃ₗ[R] Q) : AbsorbsRegular R P := by
  obtain ⟨p, s, hs⟩ := exists_retraction_regular L Q
  let φ : R ≃ₗ[R] (↥(LinearMap.ker p) × Q) :=
    ((LinearMap.exact_subtype_ker_map p).splitSurjectiveEquiv
      (Submodule.injective_subtype (LinearMap.ker p)) ⟨s, hs⟩).1
  exact ⟨(((((LinearEquiv.refl R P).prodCongr φ).trans
    (LinearEquiv.prodComm R P (↥(LinearMap.ker p) × Q))).trans
    (LinearEquiv.prodAssoc R (↥(LinearMap.ker p)) Q P)).trans
    ((LinearEquiv.refl R (↥(LinearMap.ker p))).prodCongr e)).trans φ.symm⟩

/-- **A module of class zero absorbs `R`.** Over a ring with a binary Leavitt family,
`[P] = 0` in `K₀(R)` implies `P ⊕ R ≅ R` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem absorbsRegular_of_cls_eq_zero (L : LeavittFamily R) (P : FGProj R)
    (h : AlgKZero.cls P = 0) : AbsorbsRegular R P.carrier := by
  have h1 : AddLocalization.addMonoidOf (⊤ : AddSubmonoid (AlgVMonoid R)) (AlgVMonoid.mk P) =
      AddLocalization.addMonoidOf (⊤ : AddSubmonoid (AlgVMonoid R))
        (AlgVMonoid.mk (FGProj.zero (R := R))) := by
    have h0 : AlgKZero.cls P = AlgKZero.cls (FGProj.zero (R := R)) := by
      rw [h, AlgKZero.cls_zero]
    exact h0
  obtain ⟨⟨c, _⟩, hc⟩ := (AddSubmonoid.LocalizationMap.eq_iff_exists _).1 h1
  obtain ⟨Q, rfl⟩ := Quot.exists_rep c
  have h2 : Quot.mk (FGProj.Iso (R := R)) (Q.sum P) =
      Quot.mk (FGProj.Iso (R := R)) (Q.sum (FGProj.zero (R := R))) := hc
  have hequiv : Equivalence (FGProj.Iso (R := R)) := by
    refine ⟨fun T => ⟨LinearEquiv.refl R T.carrier⟩, ?_, ?_⟩
    · intro T T' hT
      obtain ⟨f⟩ := hT
      exact ⟨f.symm⟩
    · intro T T' T'' hT hT'
      obtain ⟨f⟩ := hT
      obtain ⟨g⟩ := hT'
      exact ⟨f.trans g⟩
  obtain ⟨e⟩ := (Equivalence.eqvGen_iff hequiv).1 (Quot.eqvGen_exact h2)
  have e' : (Q.carrier × P.carrier) ≃ₗ[R] Q.carrier :=
    e.trans (LinearEquiv.prodUnique (R := R) (M := Q.carrier) (M₂ := PUnit.{u + 1}))
  exact absorbsRegular_of_prod_linearEquiv L e'

/-- **`K₀(R) = 0` iff every f.g. projective module absorbs `R`**, over a ring with a binary
Leavitt family (`simple_kazhdan_sofic_group.tex` l.733-735, sec:questions Q2). -/
theorem algKZero_trivial_iff_forall_absorbsRegular (L : LeavittFamily R) :
    (∀ z : AlgKZero R, z = 0) ↔ ∀ P : FGProj R, AbsorbsRegular R P.carrier :=
  ⟨fun h P => absorbsRegular_of_cls_eq_zero L P (h (AlgKZero.cls P)),
    fun h z => algKZero_eq_zero_of_forall_absorbsRegular L h z⟩

end GroupApproximation.Full.LVLowKZero
