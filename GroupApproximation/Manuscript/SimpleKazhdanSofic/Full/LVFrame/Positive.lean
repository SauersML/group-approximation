import GroupApproximation.Leavitt.LeavittSimplicity
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.BigOperators
import GroupApproximation.Meta.AxiomGuard

/-!
# Positive polynomials in `L_{F_2}(1,2)`

Lane `sk-leavitt-08`, Khanh (arXiv:2609.08428v1), proof of Lemma 4.1 (`lem:word-multiplier`).

Khanh, tex l.344: "Every element of $R$ is a finite sum of monomials $\alpha\beta^*$. ...
Choose expressions of this form for the $a_i$, and choose $N$ at least as large as all lengths
$|\beta|$ occurring in these expressions. Let $\gamma_1,\ldots,\gamma_t$ be all words of length
$N$. Each $a_i\gamma_j$ is a polynomial in positive words. ... Collect identical words over
$\F_2$ in all these polynomials".

## Route

Over `F_2 = ZMod 2`, a "polynomial in positive words with collected identical words" is
`posPoly S = ∑_{μ ∈ S} s_μ` for a finite set `S` of words.
* Closure under `+` (symmetric difference, since `y + y = 0`) and under `ZMod 2`-scalars.
* `s_α t_β s_γ` is `s_{α δ}` when `γ = β δ` and `0` when `|β| ≤ |γ|` and `β` is not a prefix.
* `exists_posPoly_mul_wordS`: from `exists_monomial_representation`, with `N = max |β_i|`,
  every `a s_γ` with `N ≤ |γ|` is a positive polynomial (Khanh uses `|γ| = N`; any
  `|γ| ≥ N` works and is what the multiplier step needs).

Lane LVFrame (leaf T1c of the `K₂(4, L) = ⊥` tree, `simple_kazhdan_sofic_group.tex` l.733-735):
port of the foreign module `LeavittK2/WordMultiplier/Positive.lean`, whose closure contains WIP commits.
-/

namespace GroupApproximation.Full.LVFrame

open scoped BigOperators

/-- `∑_{μ ∈ S} s_μ` in `L_{F_2}(1,2)`. -/
noncomputable def posPoly (S : Finset (List (Fin 2))) :
    BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) :=
  ∑ μ ∈ S, (BinaryLeavitt.family (ZMod 2)).wordS μ

#audit_axioms GroupApproximation.Full.LVFrame.posPoly

/-- Characteristic two. -/
theorem leavittTwo_add_self (y : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) : y + y = 0 := by
  rw [← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 by decide, zero_smul]

#audit_axioms GroupApproximation.Full.LVFrame.leavittTwo_add_self

theorem posPoly_empty : posPoly ∅ = 0 := by
  unfold posPoly
  rw [Finset.sum_empty]

#audit_axioms GroupApproximation.Full.LVFrame.posPoly_empty

theorem posPoly_insert {μ : List (Fin 2)} {S : Finset (List (Fin 2))} (h : μ ∉ S) :
    posPoly (insert μ S) = (BinaryLeavitt.family (ZMod 2)).wordS μ + posPoly S := by
  unfold posPoly
  rw [Finset.sum_insert h]

#audit_axioms GroupApproximation.Full.LVFrame.posPoly_insert

theorem exists_posPoly_wordS_add (μ : List (Fin 2)) (S : Finset (List (Fin 2))) :
    ∃ T, (BinaryLeavitt.family (ZMod 2)).wordS μ + posPoly S = posPoly T := by
  by_cases h : μ ∈ S
  · refine ⟨S.erase μ, ?_⟩
    unfold posPoly
    rw [← Finset.add_sum_erase S _ h, ← add_assoc,
      leavittTwo_add_self ((BinaryLeavitt.family (ZMod 2)).wordS μ), zero_add]
  · exact ⟨insert μ S, (posPoly_insert h).symm⟩

#audit_axioms GroupApproximation.Full.LVFrame.exists_posPoly_wordS_add

theorem exists_posPoly_add (S T : Finset (List (Fin 2))) :
    ∃ U, posPoly S + posPoly T = posPoly U := by
  induction S using Finset.induction_on with
  | empty => exact ⟨T, by rw [posPoly_empty, zero_add]⟩
  | insert μ S hμ ih =>
    obtain ⟨U, hU⟩ := ih
    obtain ⟨V, hV⟩ := exists_posPoly_wordS_add μ U
    exact ⟨V, by rw [posPoly_insert hμ, add_assoc, hU, hV]⟩

#audit_axioms GroupApproximation.Full.LVFrame.exists_posPoly_add

theorem exists_posPoly_smul (c : ZMod 2) (S : Finset (List (Fin 2))) :
    ∃ T, c • posPoly S = posPoly T := by
  rcases (show ∀ d : ZMod 2, d = 0 ∨ d = 1 by decide) c with rfl | rfl
  · exact ⟨∅, by rw [zero_smul, posPoly_empty]⟩
  · exact ⟨S, one_smul _ _⟩

#audit_axioms GroupApproximation.Full.LVFrame.exists_posPoly_smul

theorem exists_posPoly_sum {ι : Type*} (s : Finset ι)
    (f : ι → BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))
    (hf : ∀ i ∈ s, ∃ S, f i = posPoly S) : ∃ S, ∑ i ∈ s, f i = posPoly S := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by rw [Finset.sum_empty, posPoly_empty]⟩
  | insert i s hi ih =>
    obtain ⟨S, hS⟩ := hf i (Finset.mem_insert_self i s)
    obtain ⟨T, hT⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    obtain ⟨U, hU⟩ := exists_posPoly_add S T
    exact ⟨U, by rw [Finset.sum_insert hi, hS, hT, hU]⟩

#audit_axioms GroupApproximation.Full.LVFrame.exists_posPoly_sum

/-- `s_α t_β s_γ` is a positive polynomial (a single word or `0`) when `|β| ≤ |γ|`. -/
theorem exists_posPoly_monomial_mul_wordS (α β γ : List (Fin 2)) (hlen : β.length ≤ γ.length) :
    ∃ S, (BinaryLeavitt.family (ZMod 2)).wordS α * (BinaryLeavitt.family (ZMod 2)).wordT β *
      (BinaryLeavitt.family (ZMod 2)).wordS γ = posPoly S := by
  by_cases hp : β <+: γ
  · obtain ⟨e, rfl⟩ := hp
    refine ⟨{α ++ e}, ?_⟩
    unfold posPoly
    rw [Finset.sum_singleton, mul_assoc,
      LeavittFamily.wordT_mul_wordS_append_left, ← LeavittFamily.wordS_append]
  · have hgb : ¬ γ <+: β := by
      intro h
      have hge := h.eq_of_length_le hlen
      rw [hge] at hp
      exact hp (List.prefix_refl β)
    refine ⟨∅, ?_⟩
    rw [mul_assoc, LeavittFamily.wordT_mul_wordS_of_incomparable _ β γ hp hgb, mul_zero,
      posPoly_empty]

#audit_axioms GroupApproximation.Full.LVFrame.exists_posPoly_monomial_mul_wordS

/-- **Positivity after right multiplication** (tex l.344): every `a` has a depth `N` such that
`a s_γ` is a positive polynomial for every word `γ` with `N ≤ |γ|`. -/
theorem exists_posPoly_mul_wordS (a : BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :
    ∃ N : ℕ, ∀ γ : List (Fin 2), N ≤ γ.length →
      ∃ S, a * (BinaryLeavitt.family (ZMod 2)).wordS γ = posPoly S := by
  obtain ⟨n, co, al, be, rfl⟩ := BinaryLeavitt.exists_monomial_representation (ZMod 2) a
  refine ⟨Finset.univ.sup fun i => (be i).length, fun γ hγ => ?_⟩
  have key : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∃ S,
      co i • ((BinaryLeavitt.family (ZMod 2)).wordS (al i) *
        (BinaryLeavitt.family (ZMod 2)).wordT (be i)) *
        (BinaryLeavitt.family (ZMod 2)).wordS γ = posPoly S := by
    intro i _
    have hlen : (be i).length ≤ γ.length :=
      le_trans (Finset.le_sup (f := fun i => (be i).length) (Finset.mem_univ i)) hγ
    obtain ⟨S, hS⟩ := exists_posPoly_monomial_mul_wordS (al i) (be i) γ hlen
    obtain ⟨T, hT⟩ := exists_posPoly_smul (co i) S
    exact ⟨T, by rw [smul_mul_assoc, hS, hT]⟩
  rw [Finset.sum_mul]
  exact exists_posPoly_sum _ _ key

#audit_axioms GroupApproximation.Full.LVFrame.exists_posPoly_mul_wordS

end GroupApproximation.Full.LVFrame
