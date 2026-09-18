import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauDeepLeg
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauSplit
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVFPSwapRel
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVFPSplitRel
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCompleteBase
import GroupApproximation.Meta.AxiomGuard

/-!
# Hop D: a child of a short parent swap (lane bh-met-77t)

Let `(s; A → B)` be an instance with `s = (p0 a, q0 a)` a one-letter child of the short
incomparable pair `w = (p0, q0)`.  The split identity of lane bh-met-77f
(`higmanVCTauSplit_core`) gives `ψ(w) = ∏_b c_b` with `c_b := ψ(p0 b, q0 b)`, the product
taken over all letters `b` in the order of `List.finRange d`.  Suppose that
* `w` carries `A` to `B` and `(w; A → B)` is a leg (`higmanVCTauDeep_Leg`),
* each sibling `c_b` (`b ≠ a`) fixes `A`, and `(c_b; A → A)` is a leg.
Siblings commute with `c_a` (all-short relator, `higmanVCTauDeep_sibling`) and with
`T = ψ(A)`, so `ψ(w) T ψ(w)⁻¹ = c_a T c_a⁻¹` (`higmanVCTauDeep_prod_conj`), and the leg for `w`
gives `(s; A → B)` (`higmanVCTauDeep_hopD_case`).

Only commutation of the siblings with `A` is used; the scratch check `SP/bh-met-77t/deep.py`
also demands it for `B`, so it undercounts the Lean hop.

`higmanVCTauDeep_DLeg` extends a leg by Hop D (from either side); `higmanVCTauDeep_dleg`
proves it.  It is the leg notion of the crossed hop `EnvelopeHigmanVCTauDeepCross`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Siblings commute.**  For a short incomparable pair `(p0, q0)` and letters `b ≠ a`, the
swap `(p0 b, q0 b)` fixes the pair `(p0 a, q0 a)` (an all-short relator). -/
theorem higmanVCTauDeep_sibling {d : ℕ} (hd : 1 < d) {p0 q0 : List (Fin d)} {a b : Fin d}
    (h0 : ¬ p0 <+: q0) (h0' : ¬ q0 <+: p0) (hp0 : p0.length ≤ 2) (hq0 : q0.length ≤ 2)
    (hba : b ≠ a) :
    higmanVCTauShort_conjEq d (p0 ++ [b]) (q0 ++ [b]) (p0 ++ [a]) (q0 ++ [a]) (p0 ++ [a])
      (q0 ++ [a]) := by
  have hpb := higmanVFP_ext_incomp h0 h0' b b
  have hqb := higmanVFP_ext_incomp h0' h0 b b
  have hpa := higmanVFP_ext_incomp h0 h0' a a
  have hqa := higmanVFP_ext_incomp h0' h0 a a
  have hab : a ≠ b := fun h => hba h.symm
  have hfp : MapsCone (coneSwap _ _ hpb hqb) (p0 ++ [a]) (p0 ++ [a]) :=
    vgen_mapsCone_coneSwap_fix hpb hqb (higmanVFP_ne_letter p0 hab) (higmanVFP_ne_letter p0 hba)
      (higmanVFP_ext_incomp h0 h0' a b) (higmanVFP_ext_incomp h0' h0 b a)
  have hfq : MapsCone (coneSwap _ _ hpb hqb) (q0 ++ [a]) (q0 ++ [a]) :=
    vgen_mapsCone_coneSwap_fix hpb hqb (higmanVFP_ext_incomp h0' h0 a b)
      (higmanVFP_ext_incomp h0 h0' b a) (higmanVFP_ne_letter q0 hab) (higmanVFP_ne_letter q0 hba)
  exact higmanVCTauShort_allShort hd hpb hqb (higmanVFP_len_succ hp0 b) (higmanVFP_len_succ hq0 b)
    ⟨higmanVFP_len_succ hp0 a, higmanVFP_len_succ hq0 a, higmanVFP_len_succ hp0 a,
      higmanVFP_len_succ hq0 a⟩ hfp hfq hpa hqa hpa hqa

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_sibling

/-- **Hop D**: `s = (p0 a, q0 a)` is a child of the incomparable pair `w = (p0, q0)`, the
instance `(w; A → B)` is a leg, and every sibling `(p0 b, q0 b)`, `b ≠ a`, fixes `A` by a leg. -/
def higmanVCTauDeep_HopD (d n : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  ∃ (p0 q0 : List (Fin d)) (a : Fin d) (h0 : ¬ p0 <+: q0) (h0' : ¬ q0 <+: p0),
    p = p0 ++ [a] ∧ q = q0 ++ [a] ∧
    MapsCone (coneSwap p0 q0 h0 h0') x x' ∧ MapsCone (coneSwap p0 q0 h0 h0') y y' ∧
    higmanVCTauDeep_Leg d n p0 q0 x y x' y' ∧
    ∀ b : Fin d, b ≠ a →
      MapsCone (coneSwap (p0 ++ [b]) (q0 ++ [b]) (higmanVFP_ext_incomp h0 h0' b b)
          (higmanVFP_ext_incomp h0' h0 b b)) x x ∧
        MapsCone (coneSwap (p0 ++ [b]) (q0 ++ [b]) (higmanVFP_ext_incomp h0 h0' b b)
          (higmanVFP_ext_incomp h0' h0 b b)) y y ∧
        higmanVCTauDeep_Leg d n (p0 ++ [b]) (q0 ++ [b]) x y x y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_HopD

/-- `ψ` of a short incomparable pair is the product of `ψ` of its one-letter children. -/
theorem higmanVCTauDeep_psi_split {d : ℕ} (hd : 1 < d) {p0 q0 : List (Fin d)}
    (h0 : ¬ p0 <+: q0) (h0' : ¬ q0 <+: p0) :
    higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p0, q0)) =
      ((List.finRange d).map fun b =>
        higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p0 ++ [b], q0 ++ [b]))).prod := by
  simp only [higmanVCTauSplit_psi_of]
  exact higmanVCTauSplit_core hd _ p0 q0 le_rfl h0 h0'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_psi_split

/-- **Hop D case**, from the level-`n` hypotheses. -/
theorem higmanVCTauDeep_hopD_case {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hH : higmanVCTauDeep_HopD d n p q x y x' y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  obtain ⟨p0, q0, a, h0, h0', rfl, rfl, hmx0, hmy0, hL, hsib⟩ := hH
  have hp0 : p0.length ≤ 2 := higmanVC_len_le2 hp
  have hq0 : q0.length ≤ 2 := higmanVC_len_le2 hq
  have e := higmanVCTauDeep_leg hd hB hS h0 h0' (higmanVFP_len_le3 hp0) (higmanVFP_len_le3 hq0)
    hmx0 hmy0 hxy hyx hxy' hyx' hL
  have hc : ∀ b ∈ List.finRange d, b ≠ a →
      Commute (higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p0 ++ [b], q0 ++ [b])))
          (higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (x, y))) ∧
        Commute (higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p0 ++ [b], q0 ++ [b])))
          (higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p0 ++ [a], q0 ++ [a]))) := by
    intro b _ hba
    obtain ⟨hbx, hby, hLb⟩ := hsib b hba
    have e1 := higmanVCTauDeep_leg hd hB hS _ _ (higmanVFP_len_succ hp0 b)
      (higmanVFP_len_succ hq0 b) hbx hby hxy hyx hxy hyx hLb
    have e2 := higmanVCTauDeep_sibling hd h0 h0' hp0 hq0 hba
    unfold higmanVCTauShort_conjEq at e1 e2
    exact ⟨higmanVCTauDeep_commute_of_conj e1, higmanVCTauDeep_commute_of_conj e2⟩
  unfold higmanVCTauShort_conjEq at e ⊢
  rw [higmanVCTauDeep_psi_split hd h0 h0'] at e
  exact (higmanVCTauDeep_prod_conj
    (fun b => higmanVC_psi d (higmanVCTau_tau d) (FreeGroup.of (p0 ++ [b], q0 ++ [b]))) _ a _
    (List.nodup_finRange d) (List.mem_finRange a) hc).symm.trans e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_hopD_case

/-- **Deep leg**: a leg, or Hop D from `A`, or Hop D from `B` read backwards. -/
def higmanVCTauDeep_DLeg (d n : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  higmanVCTauDeep_Leg d n p q x y x' y' ∨ higmanVCTauDeep_HopD d n p q x y x' y' ∨
    higmanVCTauDeep_HopD d n p q x' y' x y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_DLeg

/-- **Deep legs are proved** from the level-`n` hypotheses. -/
theorem higmanVCTauDeep_dleg {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x')
    (hL : higmanVCTauDeep_DLeg d n p q x y x' y') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  rcases hL with hL | hH | hH
  · exact higmanVCTauDeep_leg hd hB hS hpq hqp hp hq hmx hmy hxy hyx hxy' hyx' hL
  · exact higmanVCTauDeep_hopD_case hd hB hS hp hq hH hxy hyx hxy' hyx'
  · exact higmanVCTauComm_flip_eq hp hq
      (higmanVCTauDeep_hopD_case hd hB hS hp hq hH hxy' hyx' hxy hyx)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_dleg

end GroupApproximation.BooneHigman.Metabelian.Envelope
