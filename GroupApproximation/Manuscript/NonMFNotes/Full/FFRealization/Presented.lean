import GroupApproximation.Sofic.KazhdanCliffordConstruction
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Meta.AxiomGuard

/-!
# `rem:ff-realization`: the presented group `E(P, α, a)`

Manuscript `non_mf_group_notes.tex`, Remark `rem:ff-realization`
("a small-cancellation realization"):

> Define `E(P,α,a)` from a finite presentation of `P` by adjoining `t, c`,
> imposing `tpt⁻¹ = α(p)`, `[c,p] = 1`, `c² = 1` for the chosen generators `p`
> of `P`, and making `w = [tct⁻¹, a(tct⁻¹)a⁻¹]` central.  The Clifford coset
> representation used in Proposition `prop:witness` maps `w` to its central
> involution.  Thus `w ≠ 1`, and `E(P,α,a)` has torsion.

This file defines `EPα P α a` for an arbitrary finitely presented group `P`,
an endomorphism `α` and an element `a`, and proves, over that general datum:

* the four printed relation families hold, for *every* `p ∈ P` and not only
  for the chosen generators (`ePα_stable_conj`, `ePα_c_commutator`,
  `ePα_c_sq`, `ePα_w_central`), and `w` is literally the printed word
  (`ePα_w_eq`);
* `w² = 1` is derived, not imposed (`ePα_w_sq`);
* the Clifford coset representation — the Clifford lamp group over the coset
  space `Σ / j(P)` of the ascending-HNN telescope `Σ`, extended by `Σ` —
  sends `w` to its nontrivial central involution
  (`ePα_cliffordCoset_w`), whenever `α` is injective and `a ∉ α(P)`;
* hence `w ≠ 1` (`ePα_mark_ne_one`) and `E(P,α,a)` has torsion
  (`ePα_has_torsion`, `ePα_not_isPowerTorsionFree`);
* under property (T) of `P`, `E(P,α,a)` is not MF, in both the
  unitary-sequence and the literal Carrión--Dadarlat--Eckhardt formulation
  (`ePα_not_isOperatorMF`, `ePα_not_isCDEOperatorMF`).

The remark itself prints no non-MF conclusion; the last item is the
Kazhdan--Clifford construction specialised to `E(P,α,a)`.

`EPα P α a` is the relative presentation: the free product of `P` with the
free group on `t, c`, modulo the normal closure of the finitely many printed
relators, where `p` ranges over the generating set extracted from the finite
presentation of `P`.  This is `KazhdanCliffordConstruction.Extension α a`,
and it is finitely presented (`ePα_finitelyPresented`).

No literature input is used anywhere in this file.
-/

namespace GroupApproximation.Full.NN08

open scoped commutatorElement

noncomputable section

universe w

section Presented

variable {P : Type} [Group P] [Group.IsFinitelyPresented P]

/-- **`E(P, α, a)`** (`rem:ff-realization`, `non_mf_group_notes.tex`): the
group obtained from a finite presentation of `P` by adjoining `t, c` with
`tpt⁻¹ = α(p)`, `[c,p] = 1`, `c² = 1` for the chosen generators `p`, and
making `w = [tct⁻¹, a(tct⁻¹)a⁻¹]` central. -/
abbrev EPα (P : Type) [Group P] [Group.IsFinitelyPresented P]
    (α : P →* P) (a : P) : Type :=
  KazhdanCliffordConstruction.Extension α a

/-- The copy of `P` inside `E(P, α, a)`. -/
abbrev EPα.base (α : P →* P) (a : P) : P →* EPα P α a :=
  KazhdanCliffordConstruction.iota α a

/-- The adjoined stable letter `t`. -/
abbrev EPα.t (α : P →* P) (a : P) : EPα P α a :=
  KazhdanCliffordConstruction.stable α a

/-- The adjoined involution `c`. -/
abbrev EPα.c (α : P →* P) (a : P) : EPα P α a :=
  KazhdanCliffordConstruction.lamp α a

/-- The distinguished word `w = [tct⁻¹, a(tct⁻¹)a⁻¹]`. -/
abbrev EPα.w (α : P →* P) (a : P) : EPα P α a :=
  KazhdanCliffordConstruction.mark α a

variable (α : P →* P) (a : P)

/-- `E(P, α, a)` is finitely presented. -/
theorem ePα_finitelyPresented : Group.IsFinitelyPresented (EPα P α a) :=
  KazhdanCliffordConstruction.extension_finitelyPresented α a

/-- `w` is the printed word `[tct⁻¹, a(tct⁻¹)a⁻¹]`. -/
theorem ePα_w_eq :
    EPα.w α a =
      ⁅EPα.t α a * EPα.c α a * (EPα.t α a)⁻¹,
        EPα.base α a a * (EPα.t α a * EPα.c α a * (EPα.t α a)⁻¹) *
          (EPα.base α a a)⁻¹⁆ :=
  rfl

/-- Printed relation `tpt⁻¹ = α(p)`, for every `p ∈ P`. -/
theorem ePα_stable_conj (p : P) :
    EPα.t α a * EPα.base α a p * (EPα.t α a)⁻¹ = EPα.base α a (α p) :=
  KazhdanCliffordConstruction.stable_compresses α a p

/-- Printed relation `[c, p] = 1`, for every `p ∈ P`. -/
theorem ePα_c_commutator (p : P) : ⁅EPα.c α a, EPα.base α a p⁆ = 1 :=
  commutatorElement_eq_one_iff_commute.mpr
    (KazhdanCliffordConstruction.lamp_commutes α a p)

/-- Printed relation `c² = 1`. -/
theorem ePα_c_sq : EPα.c α a ^ 2 = 1 :=
  KazhdanCliffordConstruction.lamp_sq α a

/-- Printed relation: `w` is central. -/
theorem ePα_w_central (g : EPα P α a) : Commute (EPα.w α a) g :=
  KazhdanCliffordConstruction.mark_central α a g

/-- `w² = 1`, derived from centrality and `c² = 1`. -/
theorem ePα_w_sq : EPα.w α a ^ 2 = 1 :=
  KazhdanCliffordConstruction.mark_sq α a

variable {α} {a}

/-- **The Clifford coset representation maps `w` to its central involution**
(`rem:ff-realization`, referring to `prop:witness`).  For injective `α` and
`a ∉ α(P)` there is a homomorphism from `E(P, α, a)` to the Clifford lamp
group over the cosets of the level-zero copy of `P` in the ascending-HNN
telescope, extended by that telescope, sending `w` to the Clifford sign, which
is a nontrivial central involution. -/
theorem ePα_cliffordCoset_w (hα : Function.Injective α)
    (ha : a ∉ Set.range α) :
    ∃ ρ : EPα P α a →* MarkedCompression.Ambient α hα,
      ρ (EPα.w α a) = MarkedCompression.signAmbient α hα ∧
        MarkedCompression.signAmbient α hα ≠ 1 ∧
        MarkedCompression.signAmbient α hα ^ 2 = 1 ∧
        ∀ g : MarkedCompression.Ambient α hα,
          Commute (MarkedCompression.signAmbient α hα) g :=
  ⟨KazhdanCliffordConstruction.cliffordHom α hα a ha,
    KazhdanCliffordConstruction.cliffordHom_mark α hα a ha,
    MarkedCompression.signAmbient_ne_one α hα,
    MarkedCompression.signAmbient_sq α hα,
    MarkedCompression.signAmbient_central α hα⟩

/-- **`w ≠ 1`** (`rem:ff-realization`). -/
theorem ePα_mark_ne_one (hα : Function.Injective α)
    (ha : a ∉ Set.range α) : EPα.w α a ≠ 1 :=
  KazhdanCliffordConstruction.mark_ne_one α hα a ha

/-- `P` embeds in `E(P, α, a)`. -/
theorem ePα_base_injective (hα : Function.Injective α)
    (ha : a ∉ Set.range α) : Function.Injective (EPα.base α a) :=
  KazhdanCliffordConstruction.iota_injective α hα a ha

/-- **`E(P, α, a)` has torsion** (`rem:ff-realization`): `w` is a nontrivial
involution. -/
theorem ePα_has_torsion (hα : Function.Injective α)
    (ha : a ∉ Set.range α) : ∃ x : EPα P α a, x ≠ 1 ∧ x ^ 2 = 1 :=
  ⟨EPα.w α a, ePα_mark_ne_one hα ha, ePα_w_sq α a⟩

/-- `E(P, α, a)` is not torsion-free. -/
theorem ePα_not_isPowerTorsionFree (hα : Function.Injective α)
    (ha : a ∉ Set.range α) : ¬ IsPowerTorsionFree (EPα P α a) := by
  intro htf
  exact ePα_mark_ne_one hα ha (htf (EPα.w α a) 2 (by omega) (ePα_w_sq α a))

/-- **`E(P, α, a)` is not MF** (unitary-sequence formulation), for Kazhdan `P`. -/
theorem ePα_not_isOperatorMF (hT : HasKazhdanPropertyT.{0, 0} P)
    (hα : Function.Injective α) (ha : a ∉ Set.range α) :
    ¬ IsOperatorMF (EPα P α a) :=
  KazhdanCliffordConstruction.not_isOperatorMF α hα a hT ha

/-- **`E(P, α, a)` is not MF** in the literal Carrión--Dadarlat--Eckhardt
formulation, for `P` with property (T) in its textbook complex form. -/
theorem ePα_not_isCDEOperatorMF (hT : HasKazhdanPropertyTComplex.{0, w} P)
    (hα : Function.Injective α) (ha : a ∉ Set.range α) :
    ¬ IsCDEOperatorMF (EPα P α a) := by
  obtain ⟨-, -, -, -, -, -, hMF⟩ :=
    KazhdanCliffordConstruction.kazhdanCliffordConstruction α hα a hT ha
  exact hMF

end Presented

#audit_axioms GroupApproximation.Full.NN08.ePα_w_eq
#audit_axioms GroupApproximation.Full.NN08.ePα_cliffordCoset_w
#audit_axioms GroupApproximation.Full.NN08.ePα_mark_ne_one
#audit_axioms GroupApproximation.Full.NN08.ePα_not_isPowerTorsionFree
#audit_axioms GroupApproximation.Full.NN08.ePα_not_isOperatorMF
#audit_axioms GroupApproximation.Full.NN08.ePα_not_isCDEOperatorMF

end

end GroupApproximation.Full.NN08
