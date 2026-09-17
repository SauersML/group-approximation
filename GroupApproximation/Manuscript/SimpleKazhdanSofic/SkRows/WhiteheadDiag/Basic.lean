import GroupApproximation.KOne.BlockWhitehead
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import GroupApproximation.Meta.AxiomGuard

/-!
# Whitehead's lemma over a noncommutative ring, inside `EL_n(R)`

Lane `sk-rows-12`.  This is ring-generic infrastructure on Khanh's "elementary generation" route
to the rank-four `K₂` gap behind tex 733.  It does not formalize a tex sentence by itself.

## Statements

For every associative unital ring `R` (no commutativity, no nontriviality, no division
hypothesis) and all units `u a b : Rˣ`:

* `diag_unit_inv_mem_elementary`: `diag(u, u⁻¹) ∈ EL_2(R)`;
* `diag_commutator_mem_elementary`: `diag(a b a⁻¹ b⁻¹, 1) ∈ EL_2(R)`;
* the same statements padded to `Fin n`, with `u` at `i`, `u⁻¹` at `j ≠ i` and `1` elsewhere
  (`diag_unit_inv_mem_elementary_padded`), and with `a b a⁻¹ b⁻¹` at `i` and `1` elsewhere
  whenever `2 ≤ n` (`diag_commutator_mem_elementary_padded`).

`EL_ι(R)` is `GroupApproximation.elementaryGroup ι R`, a subgroup of `(Matrix ι ι R)ˣ`.  So
"the matrix `D` lies in `EL`" is stated as `∃ g ∈ elementaryGroup ι R, (g : Matrix ι ι R) = D`.

## Truth check (on paper)

With `x₁₂(a) = !![1, a; 0, 1]` and `x₂₁(a) = !![1, 0; a, 1]`:
`w(u) := x₁₂(u) x₂₁(-u⁻¹) x₁₂(u) = !![0, u; -u⁻¹, 0]` and `w(-1) = !![0, -1; 1, 0]`, so
`w(u) w(-1) = !![u, 0; 0, u⁻¹]`.  Only `u u⁻¹ = u⁻¹ u = 1` is used, so this holds over every
ring.  For the commutator,
`diag(a, a⁻¹) · diag(b, b⁻¹) · diag((ba)⁻¹, ba) = diag(a b (ba)⁻¹, a⁻¹ b⁻¹ b a)
  = diag(a b a⁻¹ b⁻¹, 1)`.

## Route (corpus reuse)

The six-factor Whitehead word in the block of two coordinates `l ≠ m` of an arbitrary finite
index type is already proved, unconditionally, in `KOne/BlockWhitehead.lean`:
`RankNElimination.diagPairAt_self_inv_mem l m hlm x : diagPairAt l m x x⁻¹ ∈ EL_ι(R)`.
This module adds:

* `diagPairAt_whitehead_split`: the product identity
  `diag(a, a⁻¹) · diag(b, b⁻¹) · diag((ba)⁻¹, ba) = diagAt l (a b a⁻¹ b⁻¹)`;
* `diagAt_commutator_mem_of_ne`: the resulting membership, from three Whitehead factors;
* the `Fin n` padded forms and the `Fin 2` forms with `Matrix.diagonal ![_, _]`.

No `Statement` hypotheses, no cited inputs.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.WhiteheadDiag

section General

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

/-- **Whitehead's lemma at two coordinates**: `diag(u, u⁻¹)` in coordinates `l ≠ m` (and `1`
elsewhere) lies in `EL_ι(R)`.  This restates the corpus lemma
`RankNElimination.diagPairAt_self_inv_mem`. -/
theorem diagPairAt_unit_inv_mem (l m : ι) (hlm : l ≠ m) (u : Rˣ) :
    (RankNElimination.diagPairAt l m u u⁻¹ : (Matrix ι ι R)ˣ) ∈ elementaryGroup ι R :=
  RankNElimination.diagPairAt_self_inv_mem l m hlm u

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.WhiteheadDiag.diagPairAt_unit_inv_mem

/-- The second Whitehead factor with its lower entry written `b a`, not `((b a)⁻¹)⁻¹`. -/
theorem diagPairAt_inv_self_mem (l m : ι) (hlm : l ≠ m) (x : Rˣ) :
    (RankNElimination.diagPairAt l m x⁻¹ x : (Matrix ι ι R)ˣ) ∈ elementaryGroup ι R := by
  have h := RankNElimination.diagPairAt_self_inv_mem (R := R) l m hlm x⁻¹
  rwa [inv_inv] at h

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.WhiteheadDiag.diagPairAt_inv_self_mem

/-- **The Whitehead split**: `diag(a, a⁻¹) · diag(b, b⁻¹) · diag((ba)⁻¹, ba) = diag([a, b], 1)`
in the coordinates `l, m`, with `1` elsewhere. -/
theorem diagPairAt_whitehead_split (l m : ι) (a b : Rˣ) :
    (RankNElimination.diagPairAt l m a a⁻¹ : (Matrix ι ι R)ˣ) *
        RankNElimination.diagPairAt l m b b⁻¹ *
        RankNElimination.diagPairAt l m (b * a)⁻¹ (b * a) =
      RankNElimination.diagAt l (a * b * a⁻¹ * b⁻¹) := by
  rw [RankNElimination.diagPairAt_mul, RankNElimination.diagPairAt_mul,
    RankNElimination.diagAt_eq_diagPairAt l m,
    show a * b * (b * a)⁻¹ = a * b * a⁻¹ * b⁻¹ by group,
    show a⁻¹ * b⁻¹ * (b * a) = 1 by group]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.WhiteheadDiag.diagPairAt_whitehead_split

/-- **Whitehead's lemma for a commutator**: `diag(a b a⁻¹ b⁻¹)` at `l` (and `1` elsewhere) lies
in `EL_ι(R)` as soon as a second coordinate `m ≠ l` exists. -/
theorem diagAt_commutator_mem_of_ne (l m : ι) (hlm : l ≠ m) (a b : Rˣ) :
    (RankNElimination.diagAt l (a * b * a⁻¹ * b⁻¹) : (Matrix ι ι R)ˣ) ∈
      elementaryGroup ι R := by
  rw [← diagPairAt_whitehead_split l m a b]
  exact mul_mem (mul_mem (diagPairAt_unit_inv_mem l m hlm a)
    (diagPairAt_unit_inv_mem l m hlm b)) (diagPairAt_inv_self_mem l m hlm (b * a))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.WhiteheadDiag.diagAt_commutator_mem_of_ne

end General

section Padded

variable {R : Type*} [Ring R]

/-- **Padded Whitehead lemma**: for `i ≠ j` in `Fin n`, the diagonal matrix with `u` at `i`,
`u⁻¹` at `j` and `1` elsewhere lies in `EL_n(R)`. -/
theorem diag_unit_inv_mem_elementary_padded {n : ℕ} (i j : Fin n) (hij : i ≠ j) (u : Rˣ) :
    ∃ g ∈ elementaryGroup (Fin n) R, (g : Matrix (Fin n) (Fin n) R) =
      Matrix.diagonal fun k ↦
        if k = i then (u : R) else if k = j then ((u⁻¹ : Rˣ) : R) else 1 :=
  ⟨RankNElimination.diagPairAt i j u u⁻¹, diagPairAt_unit_inv_mem i j hij u,
    RankNElimination.diagPairAt_val i j u u⁻¹⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.WhiteheadDiag.diag_unit_inv_mem_elementary_padded

/-- **Padded Whitehead lemma for a commutator**: for `2 ≤ n` and any `i : Fin n`, the diagonal
matrix with `a b a⁻¹ b⁻¹` at `i` and `1` elsewhere lies in `EL_n(R)`. -/
theorem diag_commutator_mem_elementary_padded {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (a b : Rˣ) :
    ∃ g ∈ elementaryGroup (Fin n) R, (g : Matrix (Fin n) (Fin n) R) =
      Matrix.diagonal fun k ↦ if k = i then ((a * b * a⁻¹ * b⁻¹ : Rˣ) : R) else 1 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hj⟩ := exists_ne i
  exact ⟨RankNElimination.diagAt i (a * b * a⁻¹ * b⁻¹),
    diagAt_commutator_mem_of_ne i j hj.symm a b,
    RankNElimination.diagAt_val i (a * b * a⁻¹ * b⁻¹)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.WhiteheadDiag.diag_commutator_mem_elementary_padded

end Padded

section RankTwo

variable {R : Type*} [Ring R]

/-- **Whitehead's lemma in `E_2` over a noncommutative ring**: `diag(u, u⁻¹) ∈ EL_2(R)`. -/
theorem diag_unit_inv_mem_elementary (u : Rˣ) :
    ∃ g ∈ elementaryGroup (Fin 2) R, (g : Matrix (Fin 2) (Fin 2) R) =
      Matrix.diagonal ![(u : R), ((u⁻¹ : Rˣ) : R)] := by
  refine ⟨RankNElimination.diagPairAt 0 1 u u⁻¹,
    diagPairAt_unit_inv_mem 0 1 (by decide) u, ?_⟩
  rw [RankNElimination.diagPairAt_val]
  congr 1
  funext k
  fin_cases k <;> simp

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.WhiteheadDiag.diag_unit_inv_mem_elementary

/-- **Whitehead's lemma for commutators in `E_2`**: `diag(a b a⁻¹ b⁻¹, 1) ∈ EL_2(R)`. -/
theorem diag_commutator_mem_elementary (a b : Rˣ) :
    ∃ g ∈ elementaryGroup (Fin 2) R, (g : Matrix (Fin 2) (Fin 2) R) =
      Matrix.diagonal ![((a * b * a⁻¹ * b⁻¹ : Rˣ) : R), 1] := by
  refine ⟨RankNElimination.diagAt 0 (a * b * a⁻¹ * b⁻¹),
    diagAt_commutator_mem_of_ne 0 1 (by decide) a b, ?_⟩
  rw [RankNElimination.diagAt_val]
  congr 1
  funext k
  fin_cases k <;> simp

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.WhiteheadDiag.diag_commutator_mem_elementary

end RankTwo

end GroupApproximation.SimpleKazhdanSofic.SkRows.WhiteheadDiag
