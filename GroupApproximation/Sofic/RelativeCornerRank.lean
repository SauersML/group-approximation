import GroupApproximation.Sofic.NormTraceGap

/-!
# The relative rank of the averaging corner is unconstrained

`non_mf_groups_exist.tex`, in the limitations section
(`\section{Limitations of the operator-norm method}\label{sec:limits}`, the
dilution paragraph beginning *"Conversely, amplification by an identity block
separates the two normalizations exactly"*), draws a consequence the ledger
records as having no declaration:

> The relative rank of that substructure is unconstrained: padding leaves the
> averaging corner `q_n M_{d_n}(ℂ) q_n` untouched while `d_n` grows, so
> `r_n/d_n` may tend to zero while the argument uses the corner's own
> normalized trace.

`Sofic/NormTraceGap` proves the two neighbouring claims — that padding
preserves operator-norm quantities (`l2_opNorm_cornerPad`) and collapses
Hilbert–Schmidt ones (`NormModel.exists_hs_collapse`) — but not this one, which
is about the *ratio* `r_n/d_n` rather than about either norm.  The corner is
intrinsically renormalized throughout the development, so the independence
holds by construction and never had to be stated; the manuscript states it, so
it is stated here.

The three conjuncts of `manuscriptRelativeCornerRankUnconstrained` are the
sentence's three clauses.  "Untouched" is read twice, once for each quantity
the surrounding argument uses of the corner: its operator norm, and its trace.
"May tend to zero" is read as the ε-form rather than as a limit, which is what
the surrounding prose means — no particular sequence `(d_n)` is on the table,
the point is that no lower bound on `r_n/d_n` is available.
-/

namespace GroupApproximation
namespace RelativeCornerRank

open Matrix
open scoped Matrix.Norms.L2Operator

/-- **The corner survives padding, and its relative rank does not.**

* padding leaves the corner's operator norm untouched;
* padding leaves the corner's trace untouched, so an argument reading the
  corner's own normalized trace reads the same number at every padding;
* yet the relative rank `r/d` of the corner in the padded model can be made
  smaller than any prescribed bound.

Together these are the manuscript's sentence: an obstruction that renormalizes
on its own range is insensitive to padding, while any statement about the
ambient relative rank is not, so no lower bound on `r_n/d_n` may be assumed. -/
theorem manuscriptRelativeCornerRankUnconstrained :
    ∀ (Y : FiniteModel) (A : Matrix Y Y ℂ),
      (∀ m : ℕ,
        ‖(Matrix.fromBlocks A 0 0 0 :
            Matrix (padModel Y m) (padModel Y m) ℂ)‖ = ‖A‖) ∧
      (∀ m : ℕ,
        Matrix.trace (Matrix.fromBlocks A 0 0 0 :
            Matrix (padModel Y m) (padModel Y m) ℂ) = Matrix.trace A) ∧
      ∀ ε : ℝ, 0 < ε → ∃ m : ℕ,
        (Fintype.card Y : ℝ) / (Fintype.card (padModel Y m) : ℝ) < ε := by
  intro Y A
  refine ⟨fun m ↦ l2_opNorm_cornerPad Y m A, fun m ↦ ?_, ?_⟩
  · show ∑ p : Y ⊕ Fin m,
      (Matrix.fromBlocks A 0 0 0 :
        Matrix (padModel Y m) (padModel Y m) ℂ) p p = ∑ i : Y, A i i
    rw [Fintype.sum_sum_type]
    simp
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt ((Fintype.card Y : ℝ) / ε)
    refine ⟨n + 1, ?_⟩
    have hcardY : (0 : ℝ) ≤ (Fintype.card Y : ℝ) := Nat.cast_nonneg _
    have hden : (0 : ℝ) < (Fintype.card (padModel Y (n + 1)) : ℝ) := by
      rw [card_padModel]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [div_lt_iff₀ hden, card_padModel]
    push_cast
    have hlt : (Fintype.card Y : ℝ) / ε
        < (Fintype.card Y : ℝ) + ((n : ℝ) + 1) := by
      refine hn.trans_le ?_
      linarith
    have hkey : ε * ((Fintype.card Y : ℝ) / ε)
        < ε * ((Fintype.card Y : ℝ) + ((n : ℝ) + 1)) :=
      mul_lt_mul_of_pos_left hlt hε
    have hcancel : ε * ((Fintype.card Y : ℝ) / ε) = (Fintype.card Y : ℝ) := by
      field_simp
    rw [hcancel] at hkey
    linarith

end RelativeCornerRank
end GroupApproximation
