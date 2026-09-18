import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Analysis.ReducedGroupCStarSpan
import GroupApproximation.Analysis.TwoSidedRegularCommutant
import GroupApproximation.Manuscript.NonMFNotes.Full.TWW.SubgroupRegularModels

/-!
# A quasidiagonal canonical trace gives regular-character models on `⊤`

Lane TWWCore (work order WO-NN03c-2).  The target of the lane is

> `isModelled_top_of_isAmenable : IsAmenable G → TWW.IsModelled ⊤`,

the step of `thm:fixed-radical-membership` (`non_mf_group_notes.tex`,
l.1376--1378) where the reduced algebra of an amenable group is declared
quasidiagonal by Tikuisis--White--Winter.  This file is the *group-side* half
of that step, proved here unconditionally:

> if the canonical trace of `C⋆_λ(G)` is quasidiagonal, then `IsModelled ⊤`.

Given a quasidiagonal model `φₙ : C⋆_λ(G) → M_{kₙ}` of the canonical trace
(`Quasidiagonal.QuasidiagonalTraceModel`) and a finite test set `F`, the
matrices `φₙ(λ_g)` for one large `n` form a
`MFTraceRecognition.RegularCharacterModel` with bound `1`:

* contractivity is `Quasidiagonal.ucpContractive` together with `‖λ_g‖ ≤ 1`;
* star-compatibility is exact, since a unital completely positive map is
  self-adjoint (`Quasidiagonal.ucp_map_star`) and `λ_{g⁻¹} = λ_g⋆`;
* multiplicativity and trace-correctness on `F` are the model's two limits
  at the finitely many pairs and points of `F`;
* the canonical trace takes the value `δ_{g,1}` at `λ_g`, and at `g = 1` the
  trace clause is exact because `φₙ` is unital;
* the model space is nonempty, since otherwise the normalized trace of
  `φₙ(1)` would be `0` while the canonical trace of `1` is `1`.

The remaining, operator-algebraic, half (quasidiagonality of the canonical
trace for countable amenable `G`: Tikuisis--White--Winter, Ann. Math. 185
(2017), Cor. 6.1, via Schafhauser, Crelle 759 (2020), and Tu's UCT theorem)
is decomposed into work orders WO-TWWCore-1/2/3, see
`$FK/status/TWWCore.md`.
-/

namespace GroupApproximation.Full.TWWCore

open Filter ReducedGroupCStarTrace
open scoped Matrix
open scoped Matrix.Norms.L2Operator

section Translations

variable (G : Type) [Group G]

/-- The translation `λ_g`, as an element of the reduced group C⋆-algebra. -/
noncomputable def reducedTranslate (g : G) : ReducedGroupCStar G :=
  ⟨leftRegularOperator G g, leftRegularOperator_mem_reduced G g⟩

theorem reducedTranslate_mul (g h : G) :
    reducedTranslate G (g * h) = reducedTranslate G g * reducedTranslate G h :=
  Subtype.ext (leftRegularOperator_mul G g h).symm

theorem reducedTranslate_one : reducedTranslate G 1 = 1 :=
  Subtype.ext (leftRegularOperator_one G)

theorem reducedTranslate_inv (g : G) :
    reducedTranslate G g⁻¹ = star (reducedTranslate G g) :=
  Subtype.ext (GroupVonNeumann.star_leftRegularOperator G g).symm

theorem norm_reducedTranslate_le_one (g : G) : ‖reducedTranslate G g‖ ≤ 1 :=
  norm_leftRegularOperator_le_one G g

/-- The canonical trace vanishes at a nontrivial translation. -/
theorem canonicalFaithfulTracialState_reducedTranslate_of_ne {g : G}
    (hg : g ≠ 1) :
    canonicalFaithfulTracialState G (reducedTranslate G g) = 0 := by
  change (leftRegularOperator G g (deltaOne G)) 1 = 0
  rw [leftRegularOperator_apply, mul_one]
  exact TwoSidedRegularCommutant.deltaOne_apply_ne G (inv_ne_one.mpr hg)

end Translations

/-- **Quasidiagonal canonical trace ⇒ regular-character models on `⊤`.**

The group-side half of the Tikuisis--White--Winter step in
`thm:fixed-radical-membership` (`non_mf_group_notes.tex`, l.1376--1378):
matrix models of the canonical trace of `C⋆_λ(G)`, evaluated at the
translations, are contractive regular-character models on every finite
test set. -/
theorem isModelled_top_of_isQuasidiagonalTrace {G : Type} [Group G]
    (hqd : Quasidiagonal.IsQuasidiagonalTrace
      (fun T : ReducedGroupCStar G ↦ canonicalFaithfulTracialState G T)) :
    Full.TWW.IsModelled (⊤ : Subgroup G) := by
  obtain ⟨M⟩ := hqd
  intro F _ ε hε
  have hE1 : ∀ᶠ n in atTop, ∀ g ∈ F, ∀ k ∈ F,
      ‖M.map n (reducedTranslate G g * reducedTranslate G k)
        - M.map n (reducedTranslate G g) * M.map n (reducedTranslate G k)‖ < ε := by
    refine (Filter.eventually_all_finset F).2 fun g _ ↦ ?_
    refine (Filter.eventually_all_finset F).2 fun k _ ↦ ?_
    exact (tendsto_order.1
      (M.tendsto_mul (reducedTranslate G g) (reducedTranslate G k))).2 ε hε
  have hE2 : ∀ᶠ n in atTop, ∀ g ∈ F,
      ‖canonicalFaithfulTracialState G (reducedTranslate G g)
        - normTrace (M.space n) (M.map n (reducedTranslate G g))‖ < ε := by
    refine (Filter.eventually_all_finset F).2 fun g _ ↦ ?_
    exact (tendsto_order.1 (M.tendsto_trace (reducedTranslate G g))).2 ε hε
  have hE3 : ∀ᶠ n in atTop,
      ‖canonicalFaithfulTracialState G (1 : ReducedGroupCStar G)
        - normTrace (M.space n) (M.map n 1)‖ < 1 / 2 :=
    (tendsto_order.1 (M.tendsto_trace 1)).2 (1 / 2) (by norm_num)
  obtain ⟨n, hn1, hn2, hn3⟩ := (hE1.and (hE2.and hE3)).exists
  have hcard : 0 < Fintype.card (M.space n) := by
    rcases Nat.eq_zero_or_pos (Fintype.card (M.space n)) with h0 | hpos
    · exfalso
      have ht : normTrace (M.space n) (M.map n 1) = 0 := by
        rw [normTrace, h0, Nat.cast_zero, div_zero]
      have hone : canonicalFaithfulTracialState G (1 : ReducedGroupCStar G) = 1 :=
        (canonicalFaithfulTracialState G).map_one
      have hlt := hn3
      rw [hone, ht, sub_zero, norm_one] at hlt
      linarith
    · exact hpos
  have hcardC : (Fintype.card (M.space n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hcard.ne'
  refine ⟨{
    carrier := M.space n
    nonempty := hcard
    map := fun g ↦ M.map n (reducedTranslate G g)
    bounded := fun g _ ↦ ?_
    multiplicative := fun g hg k hk ↦ ?_
    star_compatible := fun g _ ↦ ?_
    trace_correct_one := fun _ ↦ ?_
    trace_correct_ne := fun g hg hg1 ↦ ?_ }⟩
  · show ‖M.map n (reducedTranslate G g)‖ ≤ 1
    exact le_trans
      (Quasidiagonal.ucpContractive.norm_le (ReducedGroupCStar G) inferInstance
        (M.space n) (M.map n) (M.map_one n) (M.completelyPositive n)
        (reducedTranslate G g))
      (norm_reducedTranslate_le_one G g)
  · show ‖M.map n (reducedTranslate G (g * k))
        - M.map n (reducedTranslate G g) * M.map n (reducedTranslate G k)‖ ≤ ε
    have hm : M.map n (reducedTranslate G (g * k))
        = M.map n (reducedTranslate G g * reducedTranslate G k) :=
      congrArg (M.map n) (reducedTranslate_mul G g k)
    rw [hm]
    exact (hn1 g hg k hk).le
  · show ‖M.map n (reducedTranslate G g⁻¹) - (M.map n (reducedTranslate G g))ᴴ‖ ≤ ε
    have hs : M.map n (reducedTranslate G g⁻¹) = (M.map n (reducedTranslate G g))ᴴ :=
      (congrArg (M.map n) (reducedTranslate_inv G g)).trans
        (Quasidiagonal.ucp_map_star (M.map n) (M.map_one n) (M.completelyPositive n)
          (reducedTranslate G g))
    rw [hs, sub_self, norm_zero]
    exact hε.le
  · show ‖Matrix.trace (M.map n (reducedTranslate G 1))
        / (Fintype.card (M.space n) : ℂ) - 1‖ ≤ ε
    have h1 : M.map n (reducedTranslate G 1) = 1 :=
      (congrArg (M.map n) (reducedTranslate_one G)).trans (M.map_one n)
    rw [h1, Matrix.trace_one, div_self hcardC, sub_self, norm_zero]
    exact hε.le
  · show ‖Matrix.trace (M.map n (reducedTranslate G g))
        / (Fintype.card (M.space n) : ℂ)‖ ≤ ε
    have h0 : canonicalFaithfulTracialState G (reducedTranslate G g) = 0 :=
      canonicalFaithfulTracialState_reducedTranslate_of_ne G hg1
    have hlt := hn2 g hg
    rw [h0, zero_sub, norm_neg] at hlt
    exact hlt.le

end GroupApproximation.Full.TWWCore
