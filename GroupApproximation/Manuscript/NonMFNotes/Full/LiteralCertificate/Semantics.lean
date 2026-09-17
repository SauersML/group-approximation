import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralCertificate.Predicate
import GroupApproximation.Manuscript.NonMFNotes.Full.RadicalArithmetic.Semantics
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:mf-radical-arithmetic`: `v ∉ Res_MF(G_P) ⟺ ∀ n ∃ d D(P,v,n,d)`

Manuscript `non_mf_group_notes.tex`, `thm:mf-radical-arithmetic`, proof:

> "Marked corona extraction and amplification, in one direction, and the
> diagonal norm-corona construction, in the other, give
> `v ∉ Res_MF(G_P) ⟺ ∀ n ∃ d D(P,v,n,d)`."

`D(P,v,n,d)` is the literal predicate `LiteralD` (defect `≤ 2^{-n-10}`,
displacement `≥ 1/2`).  The two directions are linked to NN02's open test
`MFRecognitionPi02.PassesOpen` (defect `< 1/(k+1)`, displacement `> 1/3`),
whose corona semantics NN02 proved (`NN02.not_mem_manuscriptCoronaMFResidual_iff`):

* `passesOpen_of_literalD`: `D(P,v,k,d)` passes the open test at level `k`
  (`2^{-k-10} < 1/(k+1)` and `1/2 > 1/3`).
* `exists_literalD_of_passesOpen` (amplification with the printed constants): a
  microstate passing the open test at a level `k` with `74·2^{n+10} ≤ k+1` has a
  Kronecker power of order `p ≤ 73` with relator defects at most `73/(k+1) ≤ 2^{-n-10}`
  and `v`-displacement `> 1 ≥ 1/2`.
-/

namespace GroupApproximation.Full.NN02b

open PresentationCodes AdianRabinWordProblem MFMicrostate
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The arithmetic of the amplification estimate: a relator defect `x < 1/(k+1)`,
multiplied by a Kronecker order `p ≤ 73`, stays below `2^{-n-10}` once
`74·2^{n+10} ≤ k+1`. -/
theorem amplified_defect_le {n k p : ℕ} {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x < 1 / ((k : ℝ) + 1)) (hk : 74 * (2 : ℝ) ^ (n + 10) ≤ (k : ℝ) + 1)
    (hp : p ≤ 73) : (p : ℝ) * x ≤ literalDefectBound n := by
  have hB : (0 : ℝ) < (2 : ℝ) ^ (n + 10) := by positivity
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hx' : x * ((k : ℝ) + 1) < 1 := (lt_div_iff₀ hk1).1 hx
  have hp' : (p : ℝ) ≤ 73 := by exact_mod_cast hp
  rw [literalDefectBound_eq, ← one_div, le_div_iff₀ hB]
  have h1 : (p : ℝ) * x ≤ 73 * x := mul_le_mul_of_nonneg_right hp' hx0
  have h2 : (p : ℝ) * x * (2 : ℝ) ^ (n + 10) ≤ 73 * x * (2 : ℝ) ^ (n + 10) :=
    mul_le_mul_of_nonneg_right h1 hB.le
  have h3 : x * (74 * (2 : ℝ) ^ (n + 10)) ≤ x * ((k : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hk hx0
  have h4 : 0 ≤ x * (2 : ℝ) ^ (n + 10) := mul_nonneg hx0 hB.le
  have h5 : 73 * x * (2 : ℝ) ^ (n + 10) = 73 * (x * (2 : ℝ) ^ (n + 10)) := by ring
  have h6 : x * (74 * (2 : ℝ) ^ (n + 10)) = 74 * (x * (2 : ℝ) ^ (n + 10)) := by ring
  rw [h5] at h2
  rw [h6] at h3
  linarith

/-- **Diagonal direction, first step.** `D(P,v,k,d)` passes the open test at
level `k`. -/
theorem passesOpen_of_literalD {c : PresentationCode} {v : List (ℕ × Bool)} {k d : ℕ}
    (h : LiteralD c v k d) : ∃ M : Microstate c, MFRecognitionPi02.PassesOpen c [v] k M := by
  have hd : 0 < d := literalD_dim_pos h
  obtain ⟨U, hrel, hv⟩ := h
  refine ⟨literalMicrostate c hd U, And.intro ?_ ?_⟩
  · intro r hr
    rw [literalMicrostate_len]
    exact lt_of_le_of_lt (hrel r hr) (literalDefectBound_lt k)
  · intro w hw
    rw [List.mem_singleton] at hw
    rw [hw, literalMicrostate_len]
    exact lt_of_lt_of_le (by norm_num) hv

/-- **Amplification with the printed constants.** A microstate passing the open
test at a level `k` with `74·2^{n+10} ≤ k+1` yields `D(P,v,n,d)` for some `d`. -/
theorem exists_literalD_of_passesOpen {c : PresentationCode} {v : List (ℕ × Bool)}
    {n k : ℕ} (hk : 74 * (2 : ℝ) ^ (n + 10) ≤ (k : ℝ) + 1) {M : Microstate c}
    (hM : MFRecognitionPi02.PassesOpen c [v] k M) : ∃ d, LiteralD c v n d := by
  have hY : Nonempty M.model := Fintype.card_pos_iff.mp M.card_pos
  have hsep : (1 : ℝ) / 3 ≤
      ‖((M.hom (wordOf c v) : Matrix.unitaryGroup M.model ℂ) : Matrix M.model M.model ℂ) - 1‖ :=
    (hM.2 v (List.mem_singleton_self v)).le
  obtain ⟨p, _, hpN, hpfar⟩ := OperatorNormAmplification.exists_tensorPower_far_from_one hY
    (M.hom (wordOf c v)).property (by norm_num : (0 : ℝ) < 1 / 3) hsep 73 (by norm_num)
  have hfar : 1 < (NN02.radTensorMicrostate c M.model hY M.gen p).len v := by
    rw [Microstate.len_def, NN02.radTensorMicrostate_hom]
    exact hpfar
  refine ⟨_, literalD_of_microstate (NN02.radTensorMicrostate c M.model hY M.gen p)
    (fun r hr => ?_) (by linarith)⟩
  have hr' : M.len r < 1 / ((k : ℝ) + 1) := hM.1 r hr
  calc (NN02.radTensorMicrostate c M.model hY M.gen p).len r
      ≤ (p : ℝ) * opLength M.model (FreeGroup.lift M.gen (wordOf c r)) :=
        NN02.radTensorMicrostate_len_le c M.model hY M.gen p r
    _ ≤ literalDefectBound n := amplified_defect_le (opLength_nonneg _ _) hr' hk hpN

/-- The literal and open microstate characterizations of radical non-membership
agree. -/
theorem forall_exists_literalD_iff_forall_passesOpen (c : PresentationCode)
    (v : List (ℕ × Bool)) :
    (∀ n, ∃ d, LiteralD c v n d) ↔
      ∀ k, ∃ M : Microstate c, MFRecognitionPi02.PassesOpen c [v] k M := by
  constructor
  · intro h k
    obtain ⟨d, hd⟩ := h k
    exact passesOpen_of_literalD hd
  · intro h n
    obtain ⟨M, hM⟩ := h (74 * 2 ^ (n + 10))
    have hk : 74 * (2 : ℝ) ^ (n + 10) ≤ (((74 * 2 ^ (n + 10) : ℕ) : ℝ)) + 1 := by
      push_cast
      linarith
    exact exists_literalD_of_passesOpen hk hM

/-- **`thm:mf-radical-arithmetic`, proof display, literal form**
(`non_mf_group_notes.tex`): `v ∉ Res_MF(G_P) ⟺ ∀ n ∃ d D(P,v,n,d)`, for the
literal manuscript radical `manuscriptCoronaMFResidual`. -/
theorem not_mem_manuscriptCoronaMFResidual_iff_literalD (c : PresentationCode)
    (v : List (ℕ × Bool)) :
    ev c v ∉ manuscriptCoronaMFResidual (Carrier c) ↔ ∀ n, ∃ d, LiteralD c v n d :=
  (NN02.not_mem_manuscriptCoronaMFResidual_iff c v).trans
    (forall_exists_literalD_iff_forall_passesOpen c v).symm

/-- The same equivalence for the internal unitary-sequence radical. -/
theorem not_mem_coronaMFResidual_iff_literalD (c : PresentationCode)
    (v : List (ℕ × Bool)) :
    ev c v ∉ coronaMFResidual (Carrier c) ↔ ∀ n, ∃ d, LiteralD c v n d :=
  (NN02.not_mem_coronaMFResidual_iff c v).trans
    (forall_exists_literalD_iff_forall_passesOpen c v).symm

/-- Complemented form: `v ∈ Res_MF(G_P) ⟺ ∃ n ∀ d ¬ D(P,v,n,d)`. -/
theorem mem_manuscriptCoronaMFResidual_iff_literalD (c : PresentationCode)
    (v : List (ℕ × Bool)) :
    ev c v ∈ manuscriptCoronaMFResidual (Carrier c) ↔ ∃ n, ∀ d, ¬ LiteralD c v n d := by
  constructor
  · intro hmem
    by_contra hcon
    have hall : ∀ n, ∃ d, LiteralD c v n d := by
      intro n
      by_contra hn
      exact hcon ⟨n, fun d hd => hn ⟨d, hd⟩⟩
    exact (not_mem_manuscriptCoronaMFResidual_iff_literalD c v).2 hall hmem
  · rintro ⟨n, hn⟩
    by_contra hnot
    obtain ⟨d, hd⟩ := (not_mem_manuscriptCoronaMFResidual_iff_literalD c v).1 hnot n
    exact hn d hd

/-- Closed form of the literal semantics of radical non-membership. -/
def LiteralRadicalWordSemantics : Prop :=
  ∀ (c : PresentationCode) (v : List (ℕ × Bool)),
    ev c v ∉ manuscriptCoronaMFResidual (Carrier c) ↔ ∀ n, ∃ d, LiteralD c v n d

/-- **`thm:mf-radical-arithmetic`, proof display, literal predicate, closed.** -/
theorem manuscriptLiteralRadicalWordSemantics : LiteralRadicalWordSemantics :=
  not_mem_manuscriptCoronaMFResidual_iff_literalD

end

#audit_closed_axioms GroupApproximation.Full.NN02b.manuscriptLiteralRadicalWordSemantics

end GroupApproximation.Full.NN02b
