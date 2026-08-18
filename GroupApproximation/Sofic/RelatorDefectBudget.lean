import GroupApproximation.Sofic.WeakMFUltraproduct

/-!
# Relator-defect budgets

An almost representation of a presented group is usually specified in one of
two very different ways.

* *Group-theoretically*, as a map `φ : G → U(n)` on the whole group whose
  multiplicative defect `‖φ(gh) - φ(g)φ(h)‖` is small on a finite subset
  `F₀ ⊆ G`.  This is the shape of `WeakMFApproximation`, of
  `OpAlmostRepresentation`, and of the hypothesis of `uniform_invisibility`.
* *Presentation-theoretically*, as an assignment `u : X → U(n)` of unitaries
  to the **generators**, whose **relators** are satisfied to within `δ`:
  `‖φ(r) - 1‖ ≤ δ` for every `r` in the finite relator list.

The second is the checkable one: it is a finite condition on a finite tuple of
matrices, stated entirely in terms of the printed presentation.  The first is
not: `F₀` is an unspecified finite subset of an infinite group, and nothing in
the statement says which one.

This file supplies the bridge, with an explicit constant.  Every element of
the normal closure of the relator set is a product of finitely many conjugates
of relators and their inverses; the number of conjugates needed is a fact
about the free group alone, independent of the unitaries.  Operator-norm
displacement from the identity is subadditive under multiplication and
invariant under both inversion and conjugation by unitaries
(`opLength_mul_le`, `opLength_inv`, `opLength_conj`), so a word that needs `n`
conjugates has displacement at most `n · δ` in *every* unitary assignment
whose relator defects are at most `δ`.

## What is here

* `IsRelatorProduct R n w` — `w` is a product of at most `n` conjugates of
  elements of `R` and of their inverses.  It is an inductive predicate rather
  than an existential over decompositions, so that the budget `n` is available
  as a number and can be maximized over a finite set.
* `exists_isRelatorProduct` — every element of `Subgroup.normalClosure R`
  carries some budget.  The proof is that the elements carrying a budget form
  a normal subgroup containing `R`.
* `opLength_le_of_isRelatorProduct` — the estimate: budget `n` and relator
  defect `δ` give operator-norm displacement at most `n · δ`, uniformly in the
  matrix dimension and in the unitary assignment.

## What is *not* here

Any effective value for a budget.  `exists_isRelatorProduct` produces the
number `n` from the closure induction, so `n` is as effective as the
derivation of the word from the relators — that is, computable for any word
one is willing to reduce by hand, but not bounded a priori by the statement.
Nothing in this file is a stability theorem: a small relator defect is
converted into a small multiplicative defect on a prescribed finite set, and
no claim is made that either can be repaired to an exact representation.
-/

namespace GroupApproximation
namespace RelatorDefectBudget

open Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type*} [Group G]

/-! ## The budget predicate -/

/-- `IsRelatorProduct R n w` records that `w` is a product of at most `n`
conjugates of elements of `R` and of their inverses.  The four closure
constructors are exactly the four operations under which operator-norm
displacement from the identity is controlled. -/
inductive IsRelatorProduct (R : Set G) : ℕ → G → Prop
  | one : IsRelatorProduct R 0 1
  | base {r : G} (hr : r ∈ R) : IsRelatorProduct R 1 r
  | inv {n : ℕ} {w : G} (h : IsRelatorProduct R n w) : IsRelatorProduct R n w⁻¹
  | conj {n : ℕ} {w : G} (c : G) (h : IsRelatorProduct R n w) :
      IsRelatorProduct R n (c * w * c⁻¹)
  | mul {m n : ℕ} {a b : G} (ha : IsRelatorProduct R m a)
      (hb : IsRelatorProduct R n b) : IsRelatorProduct R (m + n) (a * b)

/-- The elements carrying some finite budget. -/
def budgetSubgroup (R : Set G) : Subgroup G where
  carrier := {w : G | ∃ n : ℕ, IsRelatorProduct R n w}
  one_mem' := ⟨0, IsRelatorProduct.one⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, hm.mul hn⟩
  inv_mem' := by
    intro a ha
    obtain ⟨n, hn⟩ := ha
    exact ⟨n, hn.inv⟩

instance budgetSubgroup_normal (R : Set G) : (budgetSubgroup R).Normal where
  conj_mem := by
    intro a ha c
    obtain ⟨n, hn⟩ := ha
    exact ⟨n, hn.conj c⟩

/-- Every element of the normal closure of the relator set is a product of
boundedly many conjugates of relators. -/
theorem exists_isRelatorProduct {R : Set G} {w : G}
    (hw : w ∈ Subgroup.normalClosure R) : ∃ n : ℕ, IsRelatorProduct R n w := by
  have hsub : R ⊆ (budgetSubgroup R : Set G) := by
    intro r hr
    exact ⟨1, IsRelatorProduct.base hr⟩
  exact Subgroup.normalClosure_le_normal hsub hw

/-! ## The estimate -/

/-- **The relator-defect estimate.**  If every relator is satisfied to within
`δ` by a unitary assignment, then a word with budget `n` is displaced from the
identity by at most `n · δ`, in every matrix dimension.

The four steps of the induction are the four invariance properties of
operator-norm displacement: it vanishes at the identity, is subadditive under
products, and is unchanged by inversion and by unitary conjugation. -/
theorem opLength_le_of_isRelatorProduct {R : Set G} {Y : FiniteModel}
    (psi : G →* Matrix.unitaryGroup Y ℂ) {delta : ℝ}
    (hR : ∀ r ∈ R, opLength Y (psi r) ≤ delta) :
    ∀ {n : ℕ} {w : G}, IsRelatorProduct R n w →
      opLength Y (psi w) ≤ (n : ℝ) * delta := by
  intro n w h
  induction h with
  | one => simp
  | base hr => simpa using hR _ hr
  | inv _ ih =>
      rw [map_inv, opLength_inv]
      exact ih
  | conj c _ ih =>
      rw [map_mul, map_mul, map_inv, opLength_conj]
      exact ih
  | mul _ _ iha ihb =>
      rw [map_mul]
      refine (opLength_mul_le Y _ _).trans ?_
      push_cast
      linarith [iha, ihb]

end RelatorDefectBudget
end GroupApproximation
