import GroupApproximation.Sofic.RealizationFromUniversalGroup
import GroupApproximation.Algebra.ProductFinitePresentation
import Mathlib.Logic.Equiv.Nat

/-!
# `KC.21`: the `ContainsSquare` datum, its satisfiability, and the step the
remark compresses

`non_mf_groups_exist.tex`, `\begin{remark}[a small-cancellation realization]`
(`\label{rem:ff-realization}`).  The remark's first sentence is Fournier-Facio's
theorem, cited to `\cite[\S2]{FFF}`: a finitely presented torsion-free
property-`(T)` group `P` contains every finitely presented torsion-free group,
**in particular** a direct product `P₁ × P₂` with `Pᵢ ≅ P`.  Proof-ledger row
`KC.21` grades that `MISSING`/`literature-input`.

`Sofic.RealizationFromUniversalGroup` carries the extracted datum as the
structure `ContainsSquare P` and proves everything downstream of it (rows
`KC.22`, `KC.23`).  Two things about the datum itself were left open there, and
both are settled here.  Neither closes `KC.21`, and the module is written so
that no reader can mistake either for a proof of Fournier-Facio's theorem.

## 1.  The datum is satisfiable, so `KC.22` and `KC.23` are not vacuous

Until now nothing in the tree constructed a `ContainsSquare`, which left open
the reading that the structure is unsatisfiable and that the theorems taking it
as an argument are vacuously true.  `piContainsSquare` closes that: for any
group `G` and any index type `ι` admitting a bijection `ι ⊕ ι ≃ ι`, the
pointwise product group `ι → G` contains a copy of its own square, by
`Sum.elim` followed by reindexing.  `witnessContainsSquare` is the instance at
`ι = ℕ` through `Equiv.natSumNatEquivNat`, and
`witness_construction_hypotheses` exhibits an actual triple satisfying exactly
the three hypotheses `thm:kazhdan-clifford` asks for.  So `KC.22`'s conclusions
are drawn at least once about a real object.

**This witness is not Fournier-Facio's group and supplies nothing towards
`KC.21`.**  It is abelian --- `witness_commute`, the one separating property
proved here --- so it is very far from a property-`(T)` group, and nothing in
this module registers it as an instance, so no theorem downstream can pick it
up by accident.  What the witness settles is a question about the *structure*
--- is it inhabited at all --- not the question about *which* groups inhabit
it, which is the whole content of the citation.  It is also uncountable and so
carries no finite presentation, but that is an observation, not a theorem of
this file, and nothing here rests on it.

## 2.  The word "in particular" is an inference, and it is proved

The printed sentence does not assert `P₁ × P₂ ≤ P` directly: it deduces it from
universality, because `P × P` is itself finitely presented and torsion-free
whenever `P` is.  That deduction is `containsSquare_of_universal`, and it is
unconditional: `UniversalFPTorsionFree P` --- the citation, as a typed input
with no inhabitant anywhere --- gives `ContainsSquare P` for any finitely
presented torsion-free `P`.  The two permanence facts it consumes are
`ProductFinitePresentation.instProd` (proved in this repository, since Mathlib
closes finite presentation under free but not direct products) and Mathlib's
`Prod.instIsMulTorsionFree`.

`realization_of_universal` then runs the whole remark off that single input:
universality plus finite presentation, torsion-freeness, nontriviality and
property `(T)` of `P` give a finitely presented extension with a nontrivial
central involution that is not `CDE`-operator-MF.  So `KC.21`'s trust surface
is now exactly one statement --- `UniversalFPTorsionFree` --- rather than one
statement plus an unexamined "in particular".

## One consequence for the corpus audit, recorded rather than left to be found

Before this module, `scripts/check_non_mf_unconditional.py --audit-corpus`
listed `ContainsSquare` among the corpus-defined names that no corpus
declaration ever produces, with the fourteen declarations assuming one.
`piContainsSquare` produces one, so the name leaves that list.  **That is the
correct report and not a loss of a real signal**: the list is a vacuity-risk
detector, and the vacuity risk is precisely what is settled above.  The
literature dependency did not go anywhere --- it moved onto a name that says
what it is.  `UniversalFPTorsionFree` is on the same list, assumed by
`containsSquare_of_universal` and `realization_of_universal`, and *that* is
where a reader now finds Fournier-Facio's theorem recorded as an open input.
Nothing in this module is an `instance`, so no downstream theorem can pick the
witness up by accident, and the witness carries neither
`Group.IsFinitelyPresented` nor `HasKazhdanPropertyTComplex`, so it cannot be
fed to `realization` even deliberately.

## What remains `MISSING`, and why

`UniversalFPTorsionFree` is Fournier-Facio's theorem.  It is not proved here,
it is not provable from anything in this repository, and no declaration
inhabits it.  Row `KC.21` stays `MISSING`/`literature-input` on `FFF`.
-/

namespace GroupApproximation
namespace ContainsSquareWitness

open RealizationFromUniversalGroup KazhdanCliffordConstruction

universe u v w

/-! ## Satisfiability: a pointwise product group contains its own square -/

section Pi

variable {ι : Type u} {G : Type v} [Group G]

/-- Splitting a pair of `ι`-indexed families into an `ι ⊕ ι`-indexed one, as a
homomorphism.  The group operations on both sides are pointwise, so this is a
homomorphism for the only reason available: `Sum.elim` commutes with case
analysis on the index. -/
def elimHom : ((ι → G) × (ι → G)) →* (ι ⊕ ι → G) where
  toFun p := Sum.elim p.1 p.2
  map_one' := by funext x; cases x <;> rfl
  map_mul' p q := by funext x; cases x <;> rfl

@[simp] theorem elimHom_apply (p : (ι → G) × (ι → G)) (x : ι ⊕ ι) :
    elimHom p x = Sum.elim p.1 p.2 x := rfl

theorem elimHom_injective :
    Function.Injective (elimHom : ((ι → G) × (ι → G)) →* (ι ⊕ ι → G)) := by
  rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ hpq
  have h₁ : p₁ = q₁ := by
    funext i
    simpa using congrFun hpq (Sum.inl i)
  have h₂ : p₂ = q₂ := by
    funext i
    simpa using congrFun hpq (Sum.inr i)
  rw [h₁, h₂]

/-- Reindexing a pointwise product group along a bijection of the index set. -/
def reindexHom (e : ι ⊕ ι ≃ ι) : (ι ⊕ ι → G) →* (ι → G) where
  toFun f := fun i ↦ f (e.symm i)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem reindexHom_apply (e : ι ⊕ ι ≃ ι) (f : ι ⊕ ι → G) (i : ι) :
    reindexHom e f i = f (e.symm i) := rfl

theorem reindexHom_injective (e : ι ⊕ ι ≃ ι) :
    Function.Injective (reindexHom (G := G) e) := by
  intro f g h
  funext x
  simpa using congrFun h (e x)

/-- **A pointwise product group over a self-doubling index set contains a copy
of its own square.**  The embedding is `Sum.elim` followed by reindexing along
`ι ⊕ ι ≃ ι`, and both are injective.

This is a *satisfiability* witness for the structure, not the mathematics of
`rem:ff-realization`: the groups it produces are as far from finitely presented
Kazhdan groups as a group can be. -/
def piContainsSquare (e : ι ⊕ ι ≃ ι) : ContainsSquare (ι → G) where
  emb := (reindexHom e).comp elimHom
  emb_injective := by
    intro x y hxy
    exact elimHom_injective (reindexHom_injective e hxy)

end Pi

/-! ## The concrete witness -/

/-- The group used as the satisfiability witness: countably many copies of `ℤ`
multiplied pointwise, with no finiteness condition on the support.

It is chosen for being as unlike Fournier-Facio's group as possible while
still containing its own square: it is abelian, and `witness_commute` proves
it. -/
abbrev Witness : Type := ℕ → Multiplicative ℤ

/-- **`ContainsSquare` is satisfiable.**  `ℕ ⊕ ℕ ≃ ℕ` is
`Equiv.natSumNatEquivNat`. -/
def witnessContainsSquare : ContainsSquare Witness :=
  piContainsSquare Equiv.natSumNatEquivNat

theorem nonempty_containsSquare_witness : Nonempty (ContainsSquare Witness) :=
  ⟨witnessContainsSquare⟩

/-- **`KC.22`'s hypotheses are satisfiable.**  There is an element of the
witness at which the three inputs `thm:kazhdan-clifford` requires --- `α`
injective, `α` not surjective, and `a ∉ range α` --- all hold.  The theorems of
`Sofic.RealizationFromUniversalGroup` are therefore about a nonempty class of
data. -/
theorem witness_construction_hypotheses :
    ∃ b : Witness, b ≠ 1 ∧
      Function.Injective witnessContainsSquare.alpha ∧
        ¬ Function.Surjective witnessContainsSquare.alpha ∧
          witnessContainsSquare.emb (1, b) ∉
            Set.range witnessContainsSquare.alpha := by
  obtain ⟨b, hb⟩ := exists_ne (1 : Witness)
  exact ⟨b, hb, construction_hypotheses witnessContainsSquare hb⟩

/-- **The witness is abelian.**  Recorded so that the satisfiability result
above cannot be misread as progress on `KC.21`: what the citation asserts is
that a finitely presented torsion-free *property-`(T)`* group contains its
square, and this group is an infinite abelian one, which no property-`(T)`
group is.  This file never invokes that last implication, and does not need
to --- the separation it relies on is mechanical, not mathematical:
`Witness` carries no `HasKazhdanPropertyTComplex` and no
`Group.IsFinitelyPresented`, so `realization` cannot be applied to it. -/
theorem witness_commute (x y : Witness) : Commute x y := Commute.all x y

/-! ## The remark's "in particular", as an inference from universality -/

/-- **Fournier-Facio's theorem, as a typed input.**  `P` contains a copy of
every finitely presented torsion-free group.

**No inhabitant of this structure is constructed anywhere in this repository,
and none is postulated.**  This is proof-ledger row `KC.21`, it is cited to
`\cite[\S2]{FFF}`, and it is the single external statement the remark rests
on. -/
structure UniversalFPTorsionFree (P : Type) [Group P] : Prop where
  /-- Every finitely presented torsion-free group embeds into `P`. -/
  embeds : ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q]
    [IsMulTorsionFree Q], ∃ f : Q →* P, Function.Injective f

/-- **The word "in particular", proved.**  A finitely presented torsion-free
group that contains every finitely presented torsion-free group contains a copy
of its own square, because `P × P` is itself finitely presented
(`ProductFinitePresentation.instProd`, proved in this repository since Mathlib
closes finite presentation under free but not direct products) and torsion-free
(`Prod.instIsMulTorsionFree`).

This is the only step of the remark's first sentence that is an inference
rather than a citation, and it is now machine-checked. -/
theorem containsSquare_of_universal {P : Type} [Group P]
    [Group.IsFinitelyPresented P] [IsMulTorsionFree P]
    (h : UniversalFPTorsionFree P) : Nonempty (ContainsSquare P) := by
  obtain ⟨f, hf⟩ := h.embeds (P × P)
  exact ⟨⟨f, hf⟩⟩

/-- **`rem:ff-realization` in full, off a single literature input.**

Given Fournier-Facio's universality statement and a finitely presented,
torsion-free, nontrivial property-`(T)` group, the remark's construction runs:
there is a datum `h` and an element `b ≠ 1` at which the Kazhdan--Clifford
extension is finitely presented, carries a nontrivial central involution, and
is not `CDE`-operator-MF.

Torsion-freeness enters only through the universality input --- the
construction itself does not use it, and the extension is not torsion-free,
which is the remark's closing observation. -/
theorem realization_of_universal {P : Type} [Group P]
    [Group.IsFinitelyPresented P] [IsMulTorsionFree P] [Nontrivial P]
    (hT : HasKazhdanPropertyTComplex.{0, w} P)
    (h : UniversalFPTorsionFree P) :
    ∃ (hcs : ContainsSquare P) (b : P), b ≠ 1 ∧
      Group.IsFinitelyPresented (Extension hcs.alpha (hcs.emb (1, b))) ∧
        mark hcs.alpha (hcs.emb (1, b)) ≠ 1 ∧
          mark hcs.alpha (hcs.emb (1, b)) ^ 2 = 1 ∧
            (∀ g : Extension hcs.alpha (hcs.emb (1, b)),
              Commute (mark hcs.alpha (hcs.emb (1, b))) g) ∧
              ¬ IsCDEOperatorMF (Extension hcs.alpha (hcs.emb (1, b))) := by
  obtain ⟨hcs⟩ := containsSquare_of_universal h
  obtain ⟨b, hb⟩ := exists_ne (1 : P)
  exact ⟨hcs, b, hb, realization hT hcs hb⟩

end ContainsSquareWitness
end GroupApproximation
