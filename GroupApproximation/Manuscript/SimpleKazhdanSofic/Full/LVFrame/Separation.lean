import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVFrame.Positive
import GroupApproximation.Meta.AxiomGuard

/-!
# Word separation by the suffix `e^M f`

Lane `sk-leavitt-08`, Khanh (arXiv:2609.08428v1), before Lemma 4.1 (`lem:word-multiplier`).

Khanh, tex l.334: "If $\mu_1,\ldots,\mu_s$ are distinct positive words of lengths at most $D$
and $M>D$, then the words $\mu_i e^M f$ are pairwise prefix-incomparable. Indeed, for comparable
original words write $\mu_j=\mu_i\delta$ with $\delta$ nonempty. ... In either case $e^M f$ and
$\delta e^M f$ disagree before the shorter word ends. Original words that were
prefix-incomparable remain so. Therefore
$$(\mu_i e^M f)^*(\mu_j e^M f)=\delta_{ij}. \eqnum[eq:word-separation]$$"

Khanh, tex l.350: "Choose $M$ greater than every word length occurring in the $P_i$ and set
$x=x_0e^Mf$. Equation~\eqref{eq:word-separation} makes the support of each $P_ie^Mf$ a prefix
antichain. Choose $\eta_i$ in this support. Its coefficient is $1$, so $\eta_i^*a_ix=1$".

## Route

`e^M f` is `BinaryLeavitt.killWord M = 0^M 1`. Lengths `≤ M` suffice (the corpus lemma
`killWord_not_prefix` needs `|δ| ≤ M`, which holds since `|μ_j| ≤ M`).
* `append_killWord_not_prefix`: if `|μ| ≤ |ν|` a prefix relation forces `ν = μ δ`, `δ ≠ []`,
  and cancelling `μ` contradicts `killWord_not_prefix`; otherwise lengths forbid it.
* `wordT_append_killWord_mul_wordS`: eq:word-separation, in any Leavitt family.
* `wordT_append_killWord_mul_posPoly`: `(μ e^M f)^* P e^M f = 1` for `μ ∈ supp P`.

Lane LVFrame (leaf T1c of the `K₂(4, L) = ⊥` tree, `simple_kazhdan_sofic_group.tex` l.733-735):
port of the foreign module `LeavittK2/WordMultiplier/Separation.lean`, whose closure contains WIP commits.
-/

namespace GroupApproximation.Full.LVFrame

open scoped BigOperators

theorem append_killWord_not_prefix {μ ν : List (Fin 2)} (M : ℕ) (hν : ν.length ≤ M)
    (hne : μ ≠ ν) :
    ¬ μ ++ BinaryLeavitt.killWord M <+: ν ++ BinaryLeavitt.killWord M := by
  intro h
  by_cases hle : μ.length ≤ ν.length
  · have hp : μ <+: ν :=
      List.prefix_of_prefix_length_le ((List.prefix_append μ _).trans h)
        (List.prefix_append ν _) hle
    obtain ⟨ε, rfl⟩ := hp
    have hε : ε ≠ [] := by
      intro hε
      rw [hε, List.append_nil] at hne
      exact hne rfl
    have hεlen : ε.length ≤ M := by
      rw [List.length_append] at hν
      omega
    rw [List.append_assoc, List.prefix_append_right_inj] at h
    exact BinaryLeavitt.killWord_not_prefix ε M hε hεlen h
  · have hl := h.length_le
    rw [List.length_append, List.length_append] at hl
    omega

#audit_axioms GroupApproximation.Full.LVFrame.append_killWord_not_prefix

theorem append_killWord_ne_nil (μ : List (Fin 2)) (M : ℕ) :
    μ ++ BinaryLeavitt.killWord M ≠ [] := by
  intro hnil
  have h := congrArg List.length hnil
  rw [List.length_append, BinaryLeavitt.killWord_length, List.length_nil] at h
  omega

#audit_axioms GroupApproximation.Full.LVFrame.append_killWord_ne_nil

/-- **eq:word-separation** (tex l.334), for words of length at most `M`. -/
theorem wordT_append_killWord_mul_wordS {A : Type*} [Ring A] (L : LeavittFamily A)
    {μ ν : List (Fin 2)} (M : ℕ) (hμ : μ.length ≤ M) (hν : ν.length ≤ M) :
    L.wordT (μ ++ BinaryLeavitt.killWord M) * L.wordS (ν ++ BinaryLeavitt.killWord M) =
      if μ = ν then 1 else 0 := by
  by_cases h : μ = ν
  · subst h
    rw [if_pos rfl, LeavittFamily.wordT_mul_wordS_self]
  · rw [if_neg h]
    exact LeavittFamily.wordT_mul_wordS_of_incomparable L _ _
      (append_killWord_not_prefix M hν h) (append_killWord_not_prefix M hμ (Ne.symm h))

#audit_axioms GroupApproximation.Full.LVFrame.wordT_append_killWord_mul_wordS

/-- `(μ e^M f)^* · P · e^M f = 1` when `μ ∈ supp P` and all words of `P` have length `≤ M`
(tex l.350). -/
theorem wordT_append_killWord_mul_posPoly (M : ℕ) (S : Finset (List (Fin 2)))
    (hS : ∀ ν ∈ S, ν.length ≤ M) {μ : List (Fin 2)} (hμ : μ ∈ S) :
    (BinaryLeavitt.family (ZMod 2)).wordT (μ ++ BinaryLeavitt.killWord M) *
      (posPoly S * (BinaryLeavitt.family (ZMod 2)).wordS (BinaryLeavitt.killWord M)) = 1 := by
  unfold posPoly
  rw [Finset.sum_mul, Finset.mul_sum]
  have hterm : ∀ ν ∈ S,
      (BinaryLeavitt.family (ZMod 2)).wordT (μ ++ BinaryLeavitt.killWord M) *
        ((BinaryLeavitt.family (ZMod 2)).wordS ν *
          (BinaryLeavitt.family (ZMod 2)).wordS (BinaryLeavitt.killWord M)) =
        if μ = ν then 1 else 0 := by
    intro ν hν
    rw [← LeavittFamily.wordS_append]
    exact wordT_append_killWord_mul_wordS _ M (hS μ hμ) (hS ν hν)
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq, if_pos hμ]

#audit_axioms GroupApproximation.Full.LVFrame.wordT_append_killWord_mul_posPoly

end GroupApproximation.Full.LVFrame
