import GroupApproximation.Manuscript.NonMFNotes.Full.FFExistence.BlockSum
import GroupApproximation.Manuscript.NonMFNotes.Full.FFRealization.Realization
import GroupApproximation.Leavitt.LeavittRankEquivalence
import GroupApproximation.Endpoint.MainResults
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# `rem:ff-realization`, first sentence: which existence statement is needed

Manuscript `non_mf_group_notes.tex`, Remark `rem:ff-realization` (l.2818):

> The construction of [FFF, §2] gives a finitely presented torsion-free
> property-(T) group `P` containing `P₁ × P₂ × S`, where `Pᵢ ≅ P` and `S` is
> finitely presented, simple, and torsion-free.

Lane NN08 (`Full/FFRealization/Realization.lean`) proved everything after this
sentence, for every datum: `NN08.remFFRealization` / `NN08.ffRealization`.

## The existence statements

* `FFPrintedExistenceStatement`: the sentence as printed (`P` finitely
  presented, torsion-free, Kazhdan; `S` finitely presented, simple,
  torsion-free; an injective `P × P × S →* P`).  This is a *definition*, the
  target of a work order; nothing here assumes it.
* `FFMinimalExistenceStatement`: what `NN08.remFFRealization` actually
  consumes, so that its conclusions are instantiated at a real group: some
  finitely presented Kazhdan `P`, a datum `P × P × S ↪ P`, an injective `α`
  with image `P₁`, and `a ∈ P₂ ∖ {1}`.  Torsion-freeness of `P` and every
  property of `S` are unused by the remark's conclusions (`w ≠ 1`, torsion,
  non-MF).  The mark `a` exists as soon as `P` is nontrivial
  (`ProductDatum.exists_mark`), in particular whenever `S` is simple.
* `FFWeakExistenceStatement` (**proved**, `ffWeakExistence`): the minimal
  statement without finite presentability.

## The route used here

For a ring `R` carrying a binary Leavitt family and `m ≥ 1`, all elementary
groups `EL_{n+1}(R)`, `n ≥ 1`, are isomorphic (`LeavittFamily.rankSuccEquiv`).
Block-diagonal embedding (`BlockSum.lean`) gives
`EL_{m+1} × EL_{m+1} × EL_{m+1} ↪ EL_{3m+3} ≅ EL_{m+1}`
(`leavittProductDatum`).  Over the binary Leavitt algebra `L_k(1,2)` of a
finite field `k` these groups are finitely generated, infinite and Kazhdan
(`binaryLeavitt_finiteField_profile`).  Hence `ffWeakExistence`.

This does **not** give the printed group: `EL_{m+1}(L_k(1,2))` has torsion,
and its finite presentability is the Steinberg `K₂` finiteness question for
Leavitt algebras, which is not yet an unconditional theorem on main.  The
printed torsion-free `P` of [FFF, §2] is the subject of a work order (see
`fk/status/NN08b.md`).
-/

namespace GroupApproximation.Full.NN08b

noncomputable section

universe w

/-- **`rem:ff-realization`, first sentence, as printed.**  A target
proposition only; no theorem in this development assumes it. -/
def FFPrintedExistenceStatement : Prop :=
  ∃ (P S : Type) (_ : Group P) (_ : Group S),
    Group.IsFinitelyPresented P ∧ IsPowerTorsionFree P ∧
      HasKazhdanPropertyTComplex.{0, w} P ∧
      Group.IsFinitelyPresented S ∧ IsSimpleGroup S ∧ IsPowerTorsionFree S ∧
      Nonempty (NN08.ProductDatum P S)

/-- **The existence actually consumed by `NN08.remFFRealization`.**  A target
proposition only; no theorem in this development assumes it. -/
def FFMinimalExistenceStatement : Prop :=
  ∃ (P S : Type) (_ : Group P) (_ : Group S),
    Group.IsFinitelyPresented P ∧ HasKazhdanPropertyTComplex.{0, w} P ∧
      ∃ (D : NN08.ProductDatum P S) (α : P →* P), Function.Injective α ∧
        α.range = D.factorOne.range ∧ ∃ a : P, a ∈ D.factorTwo.range ∧ a ≠ 1

/-- **The minimal existence statement without finite presentability.**
Proved below (`ffWeakExistence`). -/
def FFWeakExistenceStatement : Prop :=
  ∃ (P : Type) (_ : Group P),
    Group.FG P ∧ Infinite P ∧ HasKazhdanPropertyTComplex.{0, w} P ∧
      ∃ (D : NN08.ProductDatum P P) (α : P →* P), Function.Injective α ∧
        α.range = D.factorOne.range ∧ ∃ a : P, a ∈ D.factorTwo.range ∧ a ≠ 1

namespace ProductDatum

variable {P S : Type} [Group P] [Group S]

/-- The second factor of a datum sends nontrivial elements to nontrivial
elements. -/
theorem factorTwo_ne_one (D : NN08.ProductDatum P S) {g : P} (hg : g ≠ 1) :
    D.factorTwo g ≠ 1 := by
  intro h1
  apply hg
  apply D.factorTwo_injective
  rw [h1, map_one]

/-- **The mark `a ∈ P₂ ∖ {1}` of `rem:ff-realization` exists** for every
datum on a nontrivial group. -/
theorem exists_mark (D : NN08.ProductDatum P S) [Nontrivial P] :
    ∃ a : P, a ∈ D.factorTwo.range ∧ a ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_ne (1 : P)
  exact ⟨D.factorTwo g, MonoidHom.mem_range.mpr ⟨g, rfl⟩,
    factorTwo_ne_one D hg⟩

end ProductDatum

variable {R : Type} [Ring R]

/-- The index equivalence `(m+1) ⊕ ((m+1) ⊕ (m+1)) ≃ 3m+3`. -/
def tripleIndexEquiv (m : ℕ) :
    Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin (m + 1)) ≃ Fin (3 * m + 2 + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin (m + 1))) finSumFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (by omega)))

/-- `EL_{(m+1) ⊕ (m+1) ⊕ (m+1)}(R) ≅ EL_{3m+3}(R) ≅ EL_{m+1}(R)` over a ring
with a binary Leavitt family. -/
def leavittTripleEquiv (L : LeavittFamily R) (m : ℕ) (hm : 0 < m) :
    elementaryGroup (Fin (m + 1) ⊕ (Fin (m + 1) ⊕ Fin (m + 1))) R ≃*
      elementaryGroup (Fin (m + 1)) R :=
  (elementaryReindexEquiv (R := R) (tripleIndexEquiv m)).trans
    (L.rankSuccEquiv (3 * m + 2) m (by omega) hm)

/-- The embedding `EL_{m+1}(R) × EL_{m+1}(R) × EL_{m+1}(R) →* EL_{m+1}(R)`. -/
def leavittTripleEmbedding (L : LeavittFamily R) (m : ℕ) (hm : 0 < m) :
    elementaryGroup (Fin (m + 1)) R × elementaryGroup (Fin (m + 1)) R ×
        elementaryGroup (Fin (m + 1)) R →*
      elementaryGroup (Fin (m + 1)) R :=
  (leavittTripleEquiv L m hm).toMonoidHom.comp
    (blockSumThree (ι := Fin (m + 1)) (κ := Fin (m + 1)) (μ := Fin (m + 1))
      (R := R))

theorem leavittTripleEmbedding_apply (L : LeavittFamily R) (m : ℕ)
    (hm : 0 < m)
    (x : elementaryGroup (Fin (m + 1)) R × elementaryGroup (Fin (m + 1)) R ×
      elementaryGroup (Fin (m + 1)) R) :
    leavittTripleEmbedding L m hm x = leavittTripleEquiv L m hm (blockSumThree x) :=
  rfl

theorem leavittTripleEmbedding_injective (L : LeavittFamily R) (m : ℕ)
    (hm : 0 < m) : Function.Injective (leavittTripleEmbedding L m hm) := by
  intro x y hxy
  rw [leavittTripleEmbedding_apply, leavittTripleEmbedding_apply] at hxy
  exact blockSumThree_injective ((leavittTripleEquiv L m hm).injective hxy)

/-- **A datum `P × P × P ≤ P` for `P = EL_{m+1}(R)`** (`rem:ff-realization`,
with `S = P`), over any ring with a binary Leavitt family and `m ≥ 1`. -/
def leavittProductDatum (L : LeavittFamily R) (m : ℕ) (hm : 0 < m) :
    NN08.ProductDatum (elementaryGroup (Fin (m + 1)) R)
      (elementaryGroup (Fin (m + 1)) R) where
  emb := leavittTripleEmbedding L m hm
  emb_injective := leavittTripleEmbedding_injective L m hm

/-- **The weak realization over a finite field.**  For every finite field `k`
and `m ≥ 1`, `P = EL_{m+1}(L_k(1,2))` is finitely generated, infinite and
Kazhdan (in the complex form used by `NN08.remFFRealization`), and the second
factor `P₂` of the datum `leavittProductDatum` contains a nontrivial
element. -/
theorem binaryLeavitt_weakDatum (k : Type) [Field k] [Finite k] (m : ℕ)
    (hm : 1 ≤ m) :
    Group.FG (BinaryLeavittEL k m) ∧ Infinite (BinaryLeavittEL k m) ∧
      HasKazhdanPropertyTComplex.{0, w} (BinaryLeavittEL k m) ∧
      ∃ a : BinaryLeavittEL k m,
        a ∈ (leavittProductDatum (BinaryLeavitt.family k) m (by omega)).factorTwo.range ∧
          a ≠ 1 := by
  obtain ⟨hfg, hinf, hT, -⟩ := binaryLeavitt_finiteField_profile k m hm
  haveI : Infinite (BinaryLeavittEL k m) := hinf
  exact ⟨hfg, hinf, hasKazhdanPropertyT_iff_textbook.mp hT,
    ProductDatum.exists_mark
      (leavittProductDatum (BinaryLeavitt.family k) m (by omega))⟩

/-- **`rem:ff-realization`, weak existence (closed).**  There is a finitely
generated infinite Kazhdan group `P` with an injective `P × P × P →* P`, an
injective `α : P →* P` with image `P₁`, and `a ∈ P₂ ∖ {1}`: every datum of the
remark except finite presentability of `P` (and the printed torsion-freeness
of `P` and properties of `S`, which the remark's conclusions do not use). -/
theorem ffWeakExistence : FFWeakExistenceStatement.{w} := by
  obtain ⟨hfg, hinf, hT, a, haP₂, ha⟩ :=
    binaryLeavitt_weakDatum.{w} (ZMod 2) 2 (by norm_num)
  exact ⟨↥(BinaryLeavittEL (ZMod 2) 2), inferInstance, hfg, hinf, hT,
    leavittProductDatum (BinaryLeavitt.family (ZMod 2)) 2 (by norm_num),
    (leavittProductDatum (BinaryLeavitt.family (ZMod 2)) 2 (by norm_num)).factorOne,
    (leavittProductDatum (BinaryLeavitt.family (ZMod 2)) 2 (by norm_num)).factorOne_injective,
    rfl, a, haP₂, ha⟩

#audit_axioms GroupApproximation.Full.NN08b.blockSumThree_injective
#audit_axioms GroupApproximation.Full.NN08b.leavittTripleEmbedding_injective
#audit_axioms GroupApproximation.Full.NN08b.binaryLeavitt_weakDatum
#audit_closed_axioms GroupApproximation.Full.NN08b.ffWeakExistence

end

end GroupApproximation.Full.NN08b
