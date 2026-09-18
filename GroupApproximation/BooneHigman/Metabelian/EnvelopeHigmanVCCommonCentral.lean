import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCommonPush
import GroupApproximation.Meta.AxiomGuard

/-!
# All-swaps presentation: kernel elements are central (lane bh-met-77d)

Let `K = Subgroup.normalClosure (higmanVC_rels d fun _ => True)` and `Q = F ⧸ K` for the
all-swaps free group `F`.

**Step A is proved here, with no hypotheses.**  For `1 < d`, every element `r` of the kernel of
`higmanVC_evalAll d` is central modulo the relators (`higmanVCCommon_ker_central`).  Equivalently,
`r z r⁻¹ z⁻¹ ∈ K` for every `z` (`higmanVCCommon_ker_comm_mem`).

Proof.  Push the deep letters through `r` (`higmanVCCommon_push`).  Because `σ_r = 1`, each
letter `(x, y)` with `|x|, |y| ≥ N` is fixed under conjugation by `r` in `Q`.  Deep splitting
(`higmanVCCommon_commute_of_letter`) extends this to every letter.

**Gap: `HigmanVCCommonCentralStatement`.**  This is `HigmanVCAllAntichainStatement` restricted to
kernel elements that are central modulo `K`.

* **It is equivalent to the target as a Prop, not strictly weaker.**
  * It implies the target (`higmanVCCommon_antichain_of_central`), because the added centrality
    hypothesis is discharged by Step A.
  * The target implies it (`higmanVCCommon_central_of_antichain`) by dropping the hypothesis.
  * As explained in `EnvelopeHigmanVCAllReduce`, no gap that yields (1) with nothing else
    supplied can be strictly weaker.
* **It is strictly smaller in proof content.**  All of the conjugation and split bookkeeping
  (Step A) is done here.  What remains is Step B: a kernel element that is *central* in `Q` is
  congruent to a word in the letters of one antichain.  That is `H₂` / normal-form content.
* **Truth.**  This is the standard presentation of Higman–Thompson `V_d`, and it is believed to be
  true, but it was not verified.
  * `scratchpad/bh-met-77d/check.py` checked the facts that Step A relies on, on random words
    for `d = 2`, with `bad = 0`:
    * affine cone tracking, with the length bound;
    * incomparability of images;
    * split refinement.
  * The check does not test Step B itself.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A kernel element commutes, modulo the relators, with every sufficiently deep incomparable
letter. -/
theorem higmanVCCommon_ker_commute_of {d : ℕ} (hd : 1 < d)
    {r : FreeGroup (List (Fin d) × List (Fin d))} (hr : r ∈ (higmanVC_evalAll d).ker) :
    ∃ N, ∀ x y : List (Fin d), N ≤ x.length → N ≤ y.length → ¬ x <+: y → ¬ y <+: x →
      Commute (higmanVCCommon_mk d r) (higmanVCCommon_mk d (FreeGroup.of (x, y))) := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨N, hN⟩ := higmanVCCommon_push hd r
  have e : higmanVCCommon_perm d r = 1 := by
    have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hr)
    exact h
  refine ⟨N, fun x y hx hy hxy hyx => ?_⟩
  obtain ⟨x', y', hx', hy', _, _, hm⟩ := hN x y hx hy hxy hyx
  rw [e] at hx' hy'
  have ex : x' = x := MapsCone.unique hx' (mapsCone_one x)
  have ey : y' = y := MapsCone.unique hy' (mapsCone_one y)
  rw [ex, ey, map_mul, map_mul, map_inv] at hm
  exact (commute_iff_eq _ _).mpr (mul_inv_eq_iff_eq_mul.mp hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_ker_commute_of

/-- **Step A.**  A kernel element is central modulo the relators. -/
theorem higmanVCCommon_ker_central {d : ℕ} (hd : 1 < d)
    {r : FreeGroup (List (Fin d) × List (Fin d))} (hr : r ∈ (higmanVC_evalAll d).ker)
    (z : FreeGroup (List (Fin d) × List (Fin d))) :
    Commute (higmanVCCommon_mk d r) (higmanVCCommon_mk d z) := by
  obtain ⟨N, hN⟩ := higmanVCCommon_ker_commute_of hd hr
  induction z using FreeGroup.induction_on with
  | C1 =>
    rw [map_one]
    exact Commute.one_right _
  | of p =>
    obtain ⟨u, v⟩ := p
    exact higmanVCCommon_commute_of_letter hN u v
  | inv_of p _ =>
    obtain ⟨u, v⟩ := p
    rw [higmanVCCommon_mk_inv_of]
    exact higmanVCCommon_commute_of_letter hN u v
  | mul g₁ g₂ ih₁ ih₂ =>
    rw [map_mul]
    exact ih₁.mul_right ih₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_ker_central

/-- **Step A, as membership.**  The commutator of a kernel element with any word is a
consequence of the relators. -/
theorem higmanVCCommon_ker_comm_mem {d : ℕ} (hd : 1 < d)
    {r : FreeGroup (List (Fin d) × List (Fin d))} (hr : r ∈ (higmanVC_evalAll d).ker)
    (z : FreeGroup (List (Fin d) × List (Fin d))) :
    r * z * r⁻¹ * z⁻¹ ∈ Subgroup.normalClosure (higmanVC_rels d fun _ => True) := by
  refine higmanVCCommon_mk_eq_one_iff.mp ?_
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, (higmanVCCommon_ker_central hd hr z).eq,
    mul_inv_cancel_right, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_ker_comm_mem

/-- **Gap (Step B).**  `HigmanVCAllAntichainStatement` restricted to kernel elements that are
central modulo the relators.  It is equivalent to the target as a Prop, and strictly smaller in
proof content: centrality is proved here.  See the module docstring. -/
def HigmanVCCommonCentralStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ r ∈ (higmanVC_evalAll d).ker,
    (∀ z : FreeGroup (List (Fin d) × List (Fin d)),
      r * z * r⁻¹ * z⁻¹ ∈ Subgroup.normalClosure (higmanVC_rels d fun _ => True)) →
    ∃ C : Finset (List (Fin d)), (∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v) ∧
      ∃ r' : FreeGroup (↥C × ↥C),
        r * (higmanVCAll_iota C r')⁻¹ ∈ Subgroup.normalClosure (higmanVC_rels d fun _ => True)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCCommonCentralStatement

/-- **The target from the gap.** -/
theorem higmanVCCommon_antichain_of_central (h : HigmanVCCommonCentralStatement) :
    HigmanVCAllAntichainStatement :=
  fun d hd r hr => h d hd r hr (higmanVCCommon_ker_comm_mem hd hr)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_antichain_of_central

/-- **The gap from the target**: the gap is equivalent to the target, not weaker. -/
theorem higmanVCCommon_central_of_antichain (h : HigmanVCAllAntichainStatement) :
    HigmanVCCommonCentralStatement :=
  fun d hd r hr _ => h d hd r hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_central_of_antichain

/-- **(1) from the gap**: the standard relators present `V_d` on all ordered pairs of words. -/
theorem higmanVCCommon_ker_le_of_central (h : HigmanVCCommonCentralStatement) (d : ℕ)
    (hd : 1 < d) :
    (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  higmanVCAll_ker_le_of_antichain (higmanVCCommon_antichain_of_central h) d hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_ker_le_of_central

/-- The gap and the long-relator extension `τ` give finite presentability of `V_d`. -/
theorem higmanVCCommon_finFP_of_central (hA : HigmanVCCommonCentralStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVFinFPStatement :=
  higmanVCAll_finFP_of_antichain_of_tau (higmanVCCommon_antichain_of_central hA) hB

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_finFP_of_central

end GroupApproximation.BooneHigman.Metabelian.Envelope
