import GroupApproximation.Monsters.FournierFacioRealization
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Algebra.GroupTorsionFree
import Mathlib.Logic.Equiv.Nat

/-!
# Where the self-embedding of the direct square comes from

Manuscript: `non_mf_groups_exist.tex`, Remark `rem:ff-realization`
(locate it by the label; line numbers drift as the surrounding sections are
edited).  Companion to
`GroupApproximation.Monsters.FournierFacioRealization`, which proves the
remark's only deduction from an abstract injection `f : P × P →* P`.

This file addresses the remaining clause of the remark, the *"in particular"*:

> His finitely presented torsion-free property-`(T)` group `P` contains a copy
> of every finitely presented torsion-free group, in particular a direct
> product `P₁ × P₂` with `Pᵢ ≅ P`.

Two things are separated here, deliberately.

* **What is mathematics, and is proved.**  The step from "contains a copy of
  every finitely presented torsion-free group" to "contains its own square"
  is the closure of that class under binary direct products.  Both closure
  facts are available in this repository as instances -- finite presentation
  of a direct product (`ProductFinitePresentation.instProd`) and
  torsion-freeness of a direct product (`IsPowerTorsionFree.prod`) -- so the
  implication is proved outright in
  `rem_ff_realization_selfSquareEmbedding_of_universal`.

* **What is literature, and is not proved.**  The existence of a finitely
  presented torsion-free property-`(T)` group that is universal for finitely
  presented torsion-free groups is an external input (Higman;
  Belegradek--Szczepanski; Chiodo, as used by Fournier-Facio).  It appears
  below only as the explicit hypothesis `huniv` of that one implication.  It
  is *not* proved here, and **nothing in the manuscript's numbered
  development depends on it**: Remark `rem:ff-realization` states no numbered
  result, carries no `\leanverified` badge, and is referenced only by a `cf.`
  pointer from the Questions preamble.  The remark itself records that
  `E(P, α, a)` has involutions whatever the base, so the small-cancellation
  base yields no conclusion the affine base does not already give.

Finally, `exists_properSelfEmbedding` shows the algebraic hypothesis consumed
by `FournierFacioRealization` is not vacuous: an explicit group is exhibited,
unconditionally, that embeds its own direct square, so that the pair
`(α, a)` demanded by Theorem `thm:kazhdan-clifford` genuinely exists.  What
that witness does *not* have -- and what only the literature input supplies --
is property `(T)` together with finite presentation.
-/

namespace GroupApproximation.Monsters.FournierFacioRealization

/-! ## The universality step -/

/-- **Remark `rem:ff-realization`, the "in particular" step.**  A group that
is finitely presented, torsion-free, and universal for finitely presented
torsion-free groups embeds its own direct square, because that class is
closed under binary direct products.

The hypothesis `huniv` is the external universality input of the remark; it is
not proved in this repository, and no numbered result of the manuscript uses
this declaration.  The mathematical content proved here is exactly the
closure step: `P × P` is again finitely presented and again torsion-free. -/
theorem rem_ff_realization_selfSquareEmbedding_of_universal
    {P : Type} [Group P] [Group.IsFinitelyPresented P]
    (hP : IsPowerTorsionFree P)
    (huniv : ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ g : Q →* P, Function.Injective g) :
    ∃ f : P × P →* P, Function.Injective f :=
  huniv (P × P) (hP.prod hP)

/-! ## An unconditional group that embeds its own direct square -/

/-- Interleaving two `ℕ`-indexed families along the bijection `ℕ ≃ ℕ ⊕ ℕ`. -/
def interleave {A : Type*} (p : (ℕ → A) × (ℕ → A)) : ℕ → A :=
  fun n ↦ Sum.elim p.1 p.2 (Equiv.natSumNatEquivNat.symm n)

@[simp] theorem interleave_apply {A : Type*} (p : (ℕ → A) × (ℕ → A)) (n : ℕ) :
    interleave p n = Sum.elim p.1 p.2 (Equiv.natSumNatEquivNat.symm n) := rfl

/-- The direct square of `ℕ → A` embeds into `ℕ → A` by interleaving. -/
def piSelfSquareEmbedding (A : Type*) [Group A] :
    (ℕ → A) × (ℕ → A) →* (ℕ → A) :=
  MonoidHom.mk' interleave (by
    intro p q
    funext n
    simp only [interleave_apply, Pi.mul_apply, Prod.fst_mul, Prod.snd_mul]
    generalize Equiv.natSumNatEquivNat.symm n = s
    cases s <;> simp)

@[simp] theorem piSelfSquareEmbedding_apply (A : Type*) [Group A]
    (p : (ℕ → A) × (ℕ → A)) : piSelfSquareEmbedding A p = interleave p := rfl

/-- Interleaving is injective: the two halves can be read back off the even
and the odd coordinates. -/
theorem piSelfSquareEmbedding_injective (A : Type*) [Group A] :
    Function.Injective (piSelfSquareEmbedding A) := by
  intro p q hpq
  have h : ∀ s : ℕ ⊕ ℕ, Sum.elim p.1 p.2 s = Sum.elim q.1 q.2 s := by
    intro s
    have hn := congrFun hpq (Equiv.natSumNatEquivNat s)
    simp only [piSelfSquareEmbedding_apply, interleave_apply,
      Equiv.symm_apply_apply] at hn
    exact hn
  refine Prod.ext ?_ ?_
  · funext k
    simpa using h (Sum.inl k)
  · funext k
    simpa using h (Sum.inr k)

/-- **The realization datum is not vacuous.**  For every nontrivial group `A`
the group `ℕ → A` carries an injective endomorphism together with an element
outside its image -- the two purely algebraic hypotheses of
Theorem `thm:kazhdan-clifford`, obtained from a self-embedding of the direct
square exactly as Remark `rem:ff-realization` obtains them.

The remaining hypotheses of that theorem, property `(T)` and finite
presentation, are what the small-cancellation construction of the remark is
needed for; this witness does not have them. -/
theorem exists_properSelfEmbedding (A : Type*) [Group A] [Nontrivial A] :
    ∃ (α : (ℕ → A) →* (ℕ → A)) (a : ℕ → A),
      Function.Injective α ∧ a ∉ Set.range α := by
  obtain ⟨a₀, ha₀⟩ := exists_ne (1 : A)
  have hb : (fun _ : ℕ ↦ a₀) ≠ (1 : ℕ → A) := by
    intro h
    exact ha₀ (congrFun h 0)
  exact ⟨selfEmbeddingEndomorphism (piSelfSquareEmbedding A),
    secondFactorElement (piSelfSquareEmbedding A) (fun _ ↦ a₀),
    rem_ff_realization_alpha_injective _ (piSelfSquareEmbedding_injective A),
    rem_ff_realization_a_notMem_range _ (piSelfSquareEmbedding_injective A)
      hb⟩

end GroupApproximation.Monsters.FournierFacioRealization
