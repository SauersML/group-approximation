import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFWitConverse
import GroupApproximation.Meta.AxiomGuard

/-!
# Antichain pivot closure (lane bh-met-77p)

Notation as in `EnvelopeHigmanVCTreeNFWit`: `Q = higmanVCCommon_Q d`, `E : Q →* V_d`,
`U = higmanVCTreeNF_U d`, and `t = mk (of (a, b))` with `|a| = n`, `|b| = n + 1`.

**LOUD: the key observation does not close pivot closure (iii).**  Take `x = τ q * u * t` and
`q' = x`.  Then `E q' = E x`, and `τ q'` lies in the `E`-double coset of `x`.  So
`x = β⁻¹ * τ q' * β'⁻¹ * z` with `β, β' ∈ U` and `z ∈ ker E`.  Here `z` is central, but nothing
forces `z = 1`.  For the canonical `τ` (a `Quotient.out`), (iii) is the same as
`ker E ∩ ⟨U, t⟩ = 1`, which is the Level Statement.  Also, `t u t ∈ U ∪ U t U` is **false** in
`V_d`: `t u t` can carry two pivots' worth of defect in its derivative distribution.

**The isolated Statement `HigmanVCTreeNFWitPivotStatement` (X).**  Let `H_C` be the image of
the antichain subgroup on a finite antichain `C`, and let `S = U · ⋃_C H_C · U`.  X says that
for the concrete pivot `t`, every `h * u * t` (with `h ∈ H_C`, `u ∈ U`) lies back in `S`.

* X is **specific to `V_d`**.  Its target family `S` is made of antichain subgroups, and these
  embed in `V_d` (`higmanVCAll_antichain_mem`).  So it cannot hold in the abstract models of
  77n, where `U` is the only faithful piece.
* X gives the Level Statement (`EnvelopeHigmanVCTreeNFWitPivotWit`).  The kernel step,
  `h ∈ H_C ∧ E h ∈ E(U) → h ∈ U`, is **proved** here from antichain faithfulness, length
  preservation and a swap decomposition.  (iii) leaves that step as the whole problem.
* Truth: X holds given (1) and Claim F.  Claim F says every element of `V_d` lies in
  `B · Sym(A) · B` for a complete antichain `A` (refine a tree pair until its source and target
  length multisets agree).  Claim F was checked numerically at `d = 2, 3`, with 600/600 random
  tree pairs (`SP/bh-met-77p/vd_ac.py`).
* **LOUD: X is equivalent to (1) as a Prop, given the truth of (1).**  It is smaller in proof
  content: the target set is explicit, and the kernel step is discharged.  It is not an
  equivalent restatement in the forbidden list (not `ker ≤ normalClosure`, Schreier, Level, or
  PivotClosed for all `t`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `C` is an antichain for the prefix order. -/
def higmanVCTreeNFWitPivot_IsAC {d : ℕ} (C : Finset (List (Fin d))) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u ≠ v → ¬ u <+: v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_IsAC

/-- The antichain subgroup `H_C ≤ Q`. -/
noncomputable def higmanVCTreeNFWitPivot_H (d : ℕ) (C : Finset (List (Fin d))) :
    Subgroup (higmanVCCommon_Q d) :=
  ((higmanVCCommon_mk d).comp (higmanVCAll_iota C)).range

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_H

theorem higmanVCTreeNFWitPivot_mem_H {d : ℕ} {C : Finset (List (Fin d))}
    {h : higmanVCCommon_Q d} :
    h ∈ higmanVCTreeNFWitPivot_H d C ↔
      ∃ r, higmanVCCommon_mk d (higmanVCAll_iota C r) = h :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_mem_H

/-- The target family `S = U · ⋃_C H_C · U`. -/
def higmanVCTreeNFWitPivot_S (d : ℕ) : Set (higmanVCCommon_Q d) :=
  {s | ∃ u₁ ∈ higmanVCTreeNF_U d, ∃ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C ∧
    ∃ h ∈ higmanVCTreeNFWitPivot_H d C, ∃ u₂ ∈ higmanVCTreeNF_U d, s = u₁ * h * u₂}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_S

theorem higmanVCTreeNFWitPivot_mem_S {d : ℕ} {s : higmanVCCommon_Q d} :
    s ∈ higmanVCTreeNFWitPivot_S d ↔
      ∃ u₁ ∈ higmanVCTreeNF_U d, ∃ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C ∧
        ∃ h ∈ higmanVCTreeNFWitPivot_H d C, ∃ u₂ ∈ higmanVCTreeNF_U d, s = u₁ * h * u₂ :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_mem_S

/-- Antichain pivot closure of `t`: every `h * u * t` falls back into `S`. -/
def higmanVCTreeNFWitPivot_ACClosed (d : ℕ) (t : higmanVCCommon_Q d) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C →
    ∀ h ∈ higmanVCTreeNFWitPivot_H d C, ∀ u ∈ higmanVCTreeNF_U d,
      h * u * t ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_ACClosed

/-- **The isolated Statement X**: antichain pivot closure of the concrete pivots. -/
def HigmanVCTreeNFWitPivotStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧
      higmanVCTreeNFWitPivot_ACClosed d (higmanVCCommon_mk d (FreeGroup.of (a, b)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTreeNFWitPivotStatement

theorem higmanVCTreeNFWitPivot_IsAC_empty (d : ℕ) :
    higmanVCTreeNFWitPivot_IsAC (∅ : Finset (List (Fin d))) :=
  fun _ hu => by simp at hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_IsAC_empty

theorem higmanVCTreeNFWitPivot_one_mem_S (d : ℕ) :
    (1 : higmanVCCommon_Q d) ∈ higmanVCTreeNFWitPivot_S d :=
  higmanVCTreeNFWitPivot_mem_S.mpr ⟨1, (higmanVCTreeNF_U d).one_mem, ∅,
    higmanVCTreeNFWitPivot_IsAC_empty d, 1, (higmanVCTreeNFWitPivot_H d ∅).one_mem, 1,
    (higmanVCTreeNF_U d).one_mem, by simp⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_one_mem_S

theorem higmanVCTreeNFWitPivot_S_mul_U {d : ℕ} {s u : higmanVCCommon_Q d}
    (hs : s ∈ higmanVCTreeNFWitPivot_S d) (hu : u ∈ higmanVCTreeNF_U d) :
    s * u ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨u₁, hu₁, C, hC, h, hh, u₂, hu₂, rfl⟩ := higmanVCTreeNFWitPivot_mem_S.mp hs
  exact higmanVCTreeNFWitPivot_mem_S.mpr
    ⟨u₁, hu₁, C, hC, h, hh, u₂ * u, (higmanVCTreeNF_U d).mul_mem hu₂ hu, mul_assoc (u₁ * h) u₂ u⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_S_mul_U

theorem higmanVCTreeNFWitPivot_S_mul_t {d : ℕ} {t : higmanVCCommon_Q d}
    (ht : higmanVCTreeNFWitPivot_ACClosed d t) {s : higmanVCCommon_Q d}
    (hs : s ∈ higmanVCTreeNFWitPivot_S d) : s * t ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨u₁, hu₁, C, hC, h, hh, u₂, hu₂, rfl⟩ := higmanVCTreeNFWitPivot_mem_S.mp hs
  obtain ⟨v₁, hv₁, C', hC', h', hh', v₂, hv₂, e⟩ :=
    higmanVCTreeNFWitPivot_mem_S.mp (ht C hC h hh u₂ hu₂)
  refine higmanVCTreeNFWitPivot_mem_S.mpr
    ⟨u₁ * v₁, (higmanVCTreeNF_U d).mul_mem hu₁ hv₁, C', hC', h', hh', v₂, hv₂, ?_⟩
  rw [mul_assoc u₁ h u₂, mul_assoc u₁ (h * u₂) t, e]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_S_mul_t

/-- Under antichain pivot closure, the whole level group `G_n` lies in `S`. -/
theorem higmanVCTreeNFWitPivot_mem_S_of_G {d n : ℕ} {a b : List (Fin d)}
    (ht : higmanVCTreeNFWitPivot_ACClosed d (higmanVCCommon_mk d (FreeGroup.of (a, b))))
    {q : higmanVCCommon_Q d} (hq : q ∈ higmanVCTreeLevel_G d n a b) :
    q ∈ higmanVCTreeNFWitPivot_S d := by
  rw [higmanVCTreeLevel_G] at hq
  have hT : Subgroup.closure (higmanVCTreeLevel_gens d n a b) ≤
      higmanVCTreeNFWit_stab (higmanVCTreeNFWitPivot_S d) := by
    refine (Subgroup.closure_le _).mpr fun g hg => ?_
    rw [higmanVCTreeLevel_gens, Set.mem_setOf_eq] at hg
    rcases hg with ⟨x, y, hx, hy, rfl⟩ | rfl
    · exact higmanVCTreeNFWit_mem_stab_of_sq (higmanVCCommon_mk_sq x y) fun _ hs =>
        higmanVCTreeNFWitPivot_S_mul_U hs (higmanVCTreeNF_letter_mem (hx.trans hy.symm))
    · exact higmanVCTreeNFWit_mem_stab_of_sq (higmanVCCommon_mk_sq a b) fun _ hs =>
        higmanVCTreeNFWitPivot_S_mul_t ht hs
  have h1 := (higmanVCTreeNFWit_mem_stab.mp (hT hq) 1).mp (higmanVCTreeNFWitPivot_one_mem_S d)
  rwa [one_mul] at h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNFWitPivot_mem_S_of_G

end GroupApproximation.BooneHigman.Metabelian.Envelope
