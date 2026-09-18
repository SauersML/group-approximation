import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllComm
import GroupApproximation.Meta.AxiomGuard

/-!
# `m(a₂, b₂)⁻¹ t ∈ H_C` for every letter `x` (lane bh-met-91x)

Notation as in `EnvelopeHigmanVCOrbitGenAtom`: `t = m(a, b)`, `a₁ = a x`, `a₂ = a x x`, and
`C = higmanVCOrbitGen_C a b x`.  `higmanVCOrbitGen_Pt_mem` needs `x` to be the head of
`List.finRange d`.  Here `x` is any letter.  Write `List.finRange d = l₁ ++ x :: l₂` and split

* `t = A₀ · m(a₁, b₁) · B₀`, where `A₀, B₀` hold the letters `m(a j, b j)`, `j ∈ l₁, l₂`;
* `m(a₁, b₁) = A₁ · P · B₁`, where `P = m(a₂, b₂)` and `A₁, B₁` hold `m(a₁ j, b₁ j)`.

Every letter of `A₀` and `A₁` has `j ≠ x`, so its words are incomparable with `a₂` and `b₂`.
Such a letter commutes with `P` (`higmanVCOrbitAll_cent0`, `higmanVCOrbitAll_cent1`).  So
`P⁻¹ t = A₀ A₁ B₁ B₀` (`higmanVCOrbitAll_elim`), and all its letters lie on leaves of `C`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- For `j ≠ x`, `m(a j, b j)` commutes with `m(a x x, b x x)`. -/
theorem higmanVCOrbitAll_cent0 {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {x j : Fin d} (hj : j ≠ x) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ [j], b ++ [j])) ∈ Subgroup.centralizer
      {higmanVCCommon_mk d (FreeGroup.of (a ++ [x] ++ [x], b ++ [x] ++ [x]))} := by
  have qa : a <+: a ++ [j] := List.prefix_append a [j]
  have qb : b <+: b ++ [j] := List.prefix_append b [j]
  have pa : a <+: a ++ [x] ++ [x] := (List.prefix_append a [x]).trans (List.prefix_append _ [x])
  have pb : b <+: b ++ [x] ++ [x] := (List.prefix_append b [x]).trans (List.prefix_append _ [x])
  have ra : a ++ [x] <+: a ++ [x] ++ [x] := List.prefix_append _ [x]
  have rb : b ++ [x] <+: b ++ [x] ++ [x] := List.prefix_append _ [x]
  have h1 : ¬ a ++ [j] <+: a ++ [x] ++ [x] := higmanVCOrbitAll_branch hj (List.prefix_refl _) ra
  have h2 : ¬ a ++ [x] ++ [x] <+: a ++ [j] :=
    higmanVCOrbitAll_branch (Ne.symm hj) ra (List.prefix_refl _)
  have h7 : ¬ b ++ [j] <+: b ++ [x] ++ [x] := higmanVCOrbitAll_branch hj (List.prefix_refl _) rb
  have h8 : ¬ b ++ [x] ++ [x] <+: b ++ [j] :=
    higmanVCOrbitAll_branch (Ne.symm hj) rb (List.prefix_refl _)
  exact higmanVCOrbitAll_comm (higmanVCOrbitGen_incomp hab hba pa pb)
    (higmanVCOrbitGen_incomp hba hab pb pa) (higmanVCOrbitGen_incomp hab hba qa qb)
    (higmanVCOrbitGen_incomp hba hab qb qa) h1 h2 (higmanVCOrbitGen_incomp hab hba qa pb)
    (higmanVCOrbitGen_incomp hba hab pb qa) (higmanVCOrbitGen_incomp hba hab qb pa)
    (higmanVCOrbitGen_incomp hab hba pa qb) h7 h8

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_cent0

/-- For `j ≠ x`, `m(a x j, b x j)` commutes with `m(a x x, b x x)`. -/
theorem higmanVCOrbitAll_cent1 {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {x j : Fin d} (hj : j ≠ x) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ [x] ++ [j], b ++ [x] ++ [j])) ∈
      Subgroup.centralizer
        {higmanVCCommon_mk d (FreeGroup.of (a ++ [x] ++ [x], b ++ [x] ++ [x]))} := by
  have i1 : ¬ a ++ [x] <+: b ++ [x] :=
    higmanVCOrbitGen_incomp hab hba (List.prefix_append a [x]) (List.prefix_append b [x])
  have i1' : ¬ b ++ [x] <+: a ++ [x] :=
    higmanVCOrbitGen_incomp hba hab (List.prefix_append b [x]) (List.prefix_append a [x])
  have qa : a ++ [x] <+: a ++ [x] ++ [j] := List.prefix_append _ [j]
  have qb : b ++ [x] <+: b ++ [x] ++ [j] := List.prefix_append _ [j]
  have pa : a ++ [x] <+: a ++ [x] ++ [x] := List.prefix_append _ [x]
  have pb : b ++ [x] <+: b ++ [x] ++ [x] := List.prefix_append _ [x]
  have h1 : ¬ a ++ [x] ++ [j] <+: a ++ [x] ++ [x] :=
    higmanVCOrbitAll_branch hj (List.prefix_refl _) (List.prefix_refl _)
  have h2 : ¬ a ++ [x] ++ [x] <+: a ++ [x] ++ [j] :=
    higmanVCOrbitAll_branch (Ne.symm hj) (List.prefix_refl _) (List.prefix_refl _)
  have h7 : ¬ b ++ [x] ++ [j] <+: b ++ [x] ++ [x] :=
    higmanVCOrbitAll_branch hj (List.prefix_refl _) (List.prefix_refl _)
  have h8 : ¬ b ++ [x] ++ [x] <+: b ++ [x] ++ [j] :=
    higmanVCOrbitAll_branch (Ne.symm hj) (List.prefix_refl _) (List.prefix_refl _)
  exact higmanVCOrbitAll_comm (higmanVCOrbitGen_incomp i1 i1' pa pb)
    (higmanVCOrbitGen_incomp i1' i1 pb pa) (higmanVCOrbitGen_incomp i1 i1' qa qb)
    (higmanVCOrbitGen_incomp i1' i1 qb qa) h1 h2 (higmanVCOrbitGen_incomp i1 i1' qa pb)
    (higmanVCOrbitGen_incomp i1' i1 pb qa) (higmanVCOrbitGen_incomp i1' i1 qb pa)
    (higmanVCOrbitGen_incomp i1 i1' pa qb) h7 h8

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_cent1

/-- `m(a₂, b₂)⁻¹ t ∈ H_C` for **every** letter `x`. -/
theorem higmanVCOrbitAll_Pt_mem {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (x : Fin d) :
    (higmanVCCommon_mk d (FreeGroup.of (a ++ [x] ++ [x], b ++ [x] ++ [x])))⁻¹ *
        higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈
      higmanVCTreeNFWitPivot_H d (higmanVCOrbitGen_C a b x) := by
  obtain ⟨l₁, l₂, hfr⟩ := List.append_of_mem (List.mem_finRange x)
  have hx : x ∉ l₁ ++ l₂ := by
    have hnd := List.nodup_finRange d
    rw [hfr] at hnd
    exact (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1
  have hne1 : ∀ j ∈ l₁, j ≠ x := fun j hj h => hx (List.mem_append_left l₂ (h ▸ hj))
  have hne2 : ∀ j ∈ l₂, j ≠ x := fun j hj h => hx (List.mem_append_right l₁ (h ▸ hj))
  have i1 : ¬ a ++ [x] <+: b ++ [x] :=
    higmanVCOrbitGen_incomp hab hba (List.prefix_append a [x]) (List.prefix_append b [x])
  have i1' : ¬ b ++ [x] <+: a ++ [x] :=
    higmanVCOrbitGen_incomp hba hab (List.prefix_append b [x]) (List.prefix_append a [x])
  have hA₀ := higmanVCOrbitGen_split_mem a b l₁ fun j hj =>
    higmanVCOrbitAll_cent0 hab hba (hne1 j hj)
  have hA₁ := higmanVCOrbitGen_split_mem (a ++ [x]) (b ++ [x]) l₁ fun j hj =>
    higmanVCOrbitAll_cent1 hab hba (hne1 j hj)
  have hc := (Subgroup.mem_centralizer_iff.mp ((Subgroup.centralizer _).mul_mem hA₀ hA₁) _
    (Set.mem_singleton _)).symm
  rw [higmanVCOrbitAll_split_mid hfr hab hba, higmanVCOrbitAll_split_mid hfr i1 i1',
    higmanVCOrbitAll_elim hc]
  refine (higmanVCTreeNFWitPivot_H d _).mul_mem ((higmanVCTreeNFWitPivot_H d _).mul_mem ?_ ?_)
    ((higmanVCTreeNFWitPivot_H d _).mul_mem ?_ ?_)
  · exact higmanVCOrbitGen_split_mem a b l₁ fun j hj =>
      higmanVCLeafExp_letter_mem_H (higmanVCOrbitGen_mem_a0 a b (hne1 j hj))
        (higmanVCOrbitGen_mem_b0 a b (hne1 j hj))
  · exact higmanVCOrbitGen_split_mem (a ++ [x]) (b ++ [x]) l₁ fun j hj =>
      higmanVCLeafExp_letter_mem_H (higmanVCOrbitGen_mem_a1 a b x j)
        (higmanVCOrbitGen_mem_b1 a b (hne1 j hj))
  · exact higmanVCOrbitGen_split_mem (a ++ [x]) (b ++ [x]) l₂ fun j hj =>
      higmanVCLeafExp_letter_mem_H (higmanVCOrbitGen_mem_a1 a b x j)
        (higmanVCOrbitGen_mem_b1 a b (hne2 j hj))
  · exact higmanVCOrbitGen_split_mem a b l₂ fun j hj =>
      higmanVCLeafExp_letter_mem_H (higmanVCOrbitGen_mem_a0 a b (hne2 j hj))
        (higmanVCOrbitGen_mem_b0 a b (hne2 j hj))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_Pt_mem

end GroupApproximation.BooneHigman.Metabelian.Envelope
