import GroupApproximation.CharClass.ChernLineEulerNatural
import GroupApproximation.CharClass.LIXVLineBundles

/-!
# The roots of `V` over the projective base

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`cc-steenrod`'s `splitRelation_V` takes the roots as a parameter agreeing with
`lineEulerOf` of the flat family on the range.  This file evaluates one of the two
kinds of line: the tautological line sitting in the block `β`, whose Euler class is
the degree-two generator of the `β.1`-th projective factor, pulled back along the
projection to that factor.

That is what makes the multiplicity come out right.  The block index `HBlk dd` is
`Σ j, Fin (dd j)`, so there are `dd j` blocks over the factor `j`, and every one of
them has the *same* class: `dd j` copies of one generator, not `dd j` unrelated
roots.

The content is one matrix identity -- the line in block `β` is the tautological line
of `ℂP^{dd β.1}` pushed along the block inclusion -- after which the three
`lineEulerOf` facts do the rest.

## Main declarations

* `blockEmb` — the block inclusion of index types.
* `vLineY_inr_eq` — **the matrix identity.**
* `lineEulerOf_vLineYBundle_inr` — **the root**, as a pulled-back generator.

## Manuscript status

Machinery.  Supplies the roots of the slice value.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The block inclusion -/

/-- The index of the block `β` sits inside the index of `V`. -/
def blockEmb (β : HBlk dd) : Fin (dd β.1 + 1) → VIdx dd := fun i => Sum.inr ⟨β, i⟩

theorem blockEmb_injective (β : HBlk dd) : Function.Injective (blockEmb β) := by
  intro i j h
  have h1 : (⟨β, i⟩ : HIdx dd) = ⟨β, j⟩ := Sum.inr.inj h
  rw [Sigma.mk.injEq] at h1
  exact eq_of_heq h1.2

/-- Evaluation at the `j`-th projective factor. -/
def evalFactor (dd : Fin ℓ → ℕ) (j : Fin ℓ) : C(baseY dd, CP (dd j)) :=
  ⟨fun y => y j, continuous_apply j⟩

/-- The tautological line of the `j`-th factor, pulled back to the base. -/
def cpTautY (dd : Fin ℓ → ℕ) (j : Fin ℓ) : Bundle (baseY dd) (Fin (dd j + 1)) :=
  comap (evalFactor dd j) (cpTaut (dd j))

theorem trace_cpTautY (dd : Fin ℓ → ℕ) (j : Fin ℓ) (y : baseY dd) :
    ((cpTautY dd j) y).trace = 1 := trace_cpTaut (dd j) _

/-! ## 2. The entries of the block line -/

/-- On its own block, `hLine` is the tautological projection. -/
theorem hLine_apply_eq (β : HBlk dd) (m : baseM dd) (i j : Fin (dd β.1 + 1)) :
    hLine β m ⟨β, i⟩ ⟨β, j⟩
      = ((m.2 β.1 : CP (dd β.1)) :
          Matrix (Fin (dd β.1 + 1)) (Fin (dd β.1 + 1)) ℂ) i j := by
  simp only [hLine]
  rw [Matrix.blockDiagonal'_apply_eq, if_pos rfl]

/-- Off its own block in the row, `hLine` vanishes. -/
theorem hLine_apply_ne_fst (β : HBlk dd) (m : baseM dd) {b₁ b₂ : HBlk dd}
    (i : Fin (dd b₁.1 + 1)) (j : Fin (dd b₂.1 + 1)) (h : b₁ ≠ β) :
    hLine β m ⟨b₁, i⟩ ⟨b₂, j⟩ = 0 := by
  by_cases hb : b₁ = b₂
  · subst hb
    simp only [hLine]
    rw [Matrix.blockDiagonal'_apply_eq, if_neg h]
    rfl
  · exact Matrix.blockDiagonal'_apply_ne
      (m' := fun b : HBlk dd => Fin (dd b.1 + 1))
      (n' := fun b : HBlk dd => Fin (dd b.1 + 1)) _ i j hb

/-- Off its own block in the column, `hLine` vanishes. -/
theorem hLine_apply_ne_snd (β : HBlk dd) (m : baseM dd) {b₂ : HBlk dd}
    (i : Fin (dd β.1 + 1)) (j : Fin (dd b₂.1 + 1)) (h : b₂ ≠ β) :
    hLine β m ⟨β, i⟩ ⟨b₂, j⟩ = 0 :=
  Matrix.blockDiagonal'_apply_ne
      (m' := fun b : HBlk dd => Fin (dd b.1 + 1))
      (n' := fun b : HBlk dd => Fin (dd b.1 + 1)) _ i j (Ne.symm h)

/-! ## 3. The matrix identity -/

/-- **The line in block `β` is the tautological line of its factor, pushed into the
block.**  Entrywise from `cc-bundle`'s three `coordIncl` conjugation lemmas against
the three entry cases above. -/
theorem vLineY_inr_eq (β : HBlk dd) (y : baseY dd) :
    vLineY (Sum.inr β) y
      = coordIncl (blockEmb β) * (cpTautY dd β.1) y * (coordIncl (blockEmb β))ᴴ := by
  have hrow : ∀ (b : HBlk dd) (i : Fin (dd b.1 + 1)), ¬ (b = β) →
      ∀ k, (Sum.inr ⟨b, i⟩ : VIdx dd) ≠ blockEmb β k :=
    fun b i hb k h => hb (congrArg Sigma.fst (Sum.inr.inj h))
  simp only [vLineY, vLine]
  ext p q
  rcases p with a | ⟨b₁, i⟩
  · rw [coordIncl_conj_apply_row (f := blockEmb β) (fun _ => Sum.inl_ne_inr) _ q]
    rcases q with c | ⟨b₂, j⟩ <;> rfl
  · rcases q with c | ⟨b₂, j⟩
    · rw [coordIncl_conj_apply_col (f := blockEmb β) (fun _ => Sum.inl_ne_inr) _
        (Sum.inr ⟨b₁, i⟩)]
      rfl
    · show hLine β ((negEThree, y) : baseM dd) ⟨b₁, i⟩ ⟨b₂, j⟩ = _
      by_cases hb1 : b₁ = β
      · by_cases hb2 : b₂ = β
        · subst hb1
          subst hb2
          rw [hLine_apply_eq]
          exact (coordIncl_conj_apply (blockEmb_injective _) _ i j).symm
        · subst hb1
          rw [hLine_apply_ne_snd _ _ i j hb2]
          exact (coordIncl_conj_apply_col (hrow b₂ j hb2) _ _).symm
      · rw [hLine_apply_ne_fst _ _ i j hb1]
        exact (coordIncl_conj_apply_row (hrow b₁ i hb1) _ _).symm

/-- The same, as bundles. -/
theorem vLineYBundle_inr_eq (β : HBlk dd) :
    vLineYBundle (Sum.inr β)
      = pushforward (blockEmb β) (blockEmb_injective β) (cpTautY dd β.1) :=
  DFunLike.ext _ _ (fun y => vLineY_inr_eq β y)

/-! ## 4. The root -/

/-- `lineEulerOf` does not depend on which proof of the trace condition it is
given, and equal bundles have equal classes. -/
theorem lineEulerOf_congr {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]
    [DecidableEq ι] {p q : Bundle X ι} (h : p = q)
    (hp : ∀ x, (p x).trace = 1) (hq : ∀ x, (q x).trace = 1) :
    lineEulerOf p hp = lineEulerOf q hq := by
  subst h
  rfl

/-- **The root.**  The Euler class of the line in block `β` is the degree-two
generator of the `β.1`-th projective factor, pulled back along the projection to
that factor.  Every block over the same factor gives the same class, which is what
makes the multiplicity `dd j` come out as `dd j` copies of one generator. -/
theorem lineEulerOf_vLineYBundle_inr (β : HBlk dd) (hd : 1 ≤ dd β.1) :
    lineEulerOf (vLineYBundle (Sum.inr β)) (trace_vLineY (Sum.inr β))
      = pull (cmap (evalFactor dd β.1)) 2 (cpGen (dd β.1) hd) := by
  refine (lineEulerOf_congr (vLineYBundle_inr_eq β) _
    (CPn.trace_pushforward_one (blockEmb β) (blockEmb_injective β) (cpTautY dd β.1)
      (trace_cpTautY dd β.1))).trans ?_
  refine (lineEulerOf_pushforward (blockEmb β) (blockEmb_injective β)
    (cpTautY dd β.1) (trace_cpTautY dd β.1)).trans ?_
  refine (lineEulerOf_comap (evalFactor dd β.1) (cpTaut (dd β.1))
    (trace_cpTaut (dd β.1))).trans ?_
  exact congrArg (pull (cmap (evalFactor dd β.1)) 2) (lineEulerOf_cpTaut (dd β.1) hd)

end

end LH
end CharClass
end GroupApproximation
