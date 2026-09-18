import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBridgeWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Explicit descent chains through a fresh bridge (lane bh-met-77q)

Let `(x, y)` be a long incomparable pair, `m` its longer word (the first one on a tie), `o`
the other one, and `t = (P, Q)` with `P = descP m o`, `Q = take 3 m` its canonical descent
pair.  Let `s = (p, q)` be a short pair that lowers the level of `(x, y)`.

A word `F` is **fresh** (`higmanVCTauBridge_Fresh`) when `|F| ≤ 2` and `F` is incomparable with
`P`, `Q`, `x`, `y`, `p` and `q`.  For a fresh `F` the pair `w = (F, Q)` is a **bridge**
(`higmanVCTauBridge_core`):

* `w` is a node: it carries `m ↦ F ++ drop 3 m` and `o` to `F ++ drop 3 o` or to itself;
* `w → t` is an edge: `w` carries `P ↦ P`, `Q ↦ F` and fixes `C_t = (dM, dO)`;
* `s → w` is an edge: `s` fixes `F`, carries `Q` to a short word
  (`higmanVCTauBridge_s_on_Q`), and carries `C_w` to a pair of level `< n`.

So `root t — w — s` is a descent chain (`higmanVCTauBridge_chain_of_fresh`), with both links
being edges into the root side.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `F` is a fresh bridge letter-word for the instance `s = (p, q)` at `(x, y)`. -/
def higmanVCTauBridge_Fresh (d : ℕ) (p q x y F : List (Fin d)) : Prop :=
  F.length ≤ 2 ∧ (¬ F <+: higmanVCTau_pP (x, y) ∧ ¬ higmanVCTau_pP (x, y) <+: F) ∧
    (¬ F <+: higmanVCTau_pQ (x, y) ∧ ¬ higmanVCTau_pQ (x, y) <+: F) ∧
    (¬ F <+: x ∧ ¬ x <+: F) ∧ (¬ F <+: y ∧ ¬ y <+: F) ∧
    (¬ F <+: p ∧ ¬ p <+: F) ∧ (¬ F <+: q ∧ ¬ q <+: F)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_Fresh

/-- **The bridge.**  For a main word `m`, the other word `o`, a level-lowering short swap
`s = (p, q)` and a fresh `F`: the canonical node `t`, the bridge node `w = (F, take 3 m)`,
and the edges `w → t` and `s → w`. -/
theorem higmanVCTauBridge_core {d : ℕ} (hd : 1 < d) {m o p q m' o' F : List (Fin d)}
    (hm : 4 ≤ m.length) (hom : ¬ o <+: m)
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hsm : MapsCone (coneSwap p q hpq hqp) m m') (hso : MapsCone (coneSwap p q hpq hqp) o o')
    (hlt : m'.length + o'.length < m.length + o.length) (hF : F.length ≤ 2)
    (hFP : ¬ F <+: higmanVCTau_descP m o) (hPF : ¬ higmanVCTau_descP m o <+: F)
    (hFQ : ¬ F <+: m.take 3) (hQF : ¬ m.take 3 <+: F) (hFo : ¬ F <+: o) (hoF : ¬ o <+: F)
    (hFp : ¬ F <+: p) (hpF : ¬ p <+: F) (hFq : ¬ F <+: q) (hqF : ¬ q <+: F) :
    ∃ X0 Y0 X1 Y1 : List (Fin d),
      higmanVCTauTight_Node d m o (higmanVCTau_descP m o) (m.take 3) X0 Y0 ∧
      higmanVCTauTight_Node d m o F (m.take 3) X1 Y1 ∧
      higmanVCTauTight_Edge d (m.length + o.length) F (m.take 3)
        (higmanVCTau_descP m o) (m.take 3) X0 Y0 ∧
      higmanVCTauTight_Edge d (m.length + o.length) p q F (m.take 3) X1 Y1 := by
  obtain ⟨hPQ, hQP, hPl, hQl, hdM, hdO, hlM, hlO, -⟩ := higmanVCTauConj_main_descent hd hm hom
  have hss := coneSwap_mul_self hPQ hQP
  have hN0 := higmanVCTauBridge_mkNode (higmanVCTauBridge_mkStep hPQ hQP hPl hQl
    (higmanVCTauConj_mapsCone_symm hdM hss) (higmanVCTauConj_mapsCone_symm hdO hss))
    (by omega)
  have hQ3 : (m.take 3).length = 3 := List.length_take_of_le (by omega)
  have hmQ : m.take 3 ++ m.drop 3 = m := List.take_append_drop 3 m
  -- the bridge swap `w = (F, Q)`
  have wQ := mapsCone_coneSwap_right hFQ hQF
  have wP : MapsCone (coneSwap F (m.take 3) hFQ hQF) (higmanVCTau_descP m o)
      (higmanVCTau_descP m o) := vgen_mapsCone_coneSwap_fix hFQ hQF hPF hFP hPQ hQP
  have wm : MapsCone (coneSwap F (m.take 3) hFQ hQF) m (F ++ m.drop 3) := by
    have h := wQ.append (m.drop 3)
    rwa [hmQ] at h
  have wdM : MapsCone (coneSwap F (m.take 3) hFQ hQF) (higmanVCTau_dM m o)
      (higmanVCTau_dM m o) := by
    rw [higmanVCTau_dM]
    exact wP.append (m.drop 3)
  -- the level-lowering swap `s = (p, q)`
  obtain ⟨⟨Q1, sQ, hQ1⟩, ho'⟩ := higmanVCTauBridge_s_on_Q hd hpq hqp hp hq hm hsm hso hlt
  have sF : MapsCone (coneSwap p q hpq hqp) F F :=
    vgen_mapsCone_coneSwap_fix hpq hqp hFp hpF hFq hqF
  have hY : ∃ Y1 Y2 : List (Fin d), MapsCone (coneSwap F (m.take 3) hFQ hQF) o Y1 ∧
      MapsCone (coneSwap F (m.take 3) hFQ hQF) (higmanVCTau_dO m o) (higmanVCTau_dO m o) ∧
      MapsCone (coneSwap p q hpq hqp) Y1 Y2 ∧ Y1.length ≤ o.length ∧
      Y2.length ≤ o.length := by
    by_cases hQo : m.take 3 <+: o
    · have hq3 : m.take 3 = o.take 3 := by
        have h' := List.prefix_iff_eq_take.mp hQo
        rwa [hQ3] at h'
      have hoQ : m.take 3 ++ o.drop 3 = o := by
        rw [hq3]
        exact List.take_append_drop 3 o
      have wo := wQ.append (o.drop 3)
      rw [hoQ] at wo
      have hle := hQo.length_le
      have hlo : (F ++ o.drop 3).length ≤ o.length := by
        rw [List.length_append, List.length_drop]
        omega
      refine ⟨F ++ o.drop 3, F ++ o.drop 3, wo, ?_, sF.append (o.drop 3), hlo, hlo⟩
      rw [higmanVCTau_dO, if_pos hQo]
      exact wP.append (o.drop 3)
    · have wo : MapsCone (coneSwap F (m.take 3) hFQ hQF) o o :=
        vgen_mapsCone_coneSwap_fix hFQ hQF hoF hFo
          (fun h => hom (h.trans (List.take_prefix 3 m))) hQo
      refine ⟨o, o', wo, ?_, hso, Nat.le_refl _, ho'⟩
      rw [higmanVCTau_dO, if_neg hQo]
      exact wo
  obtain ⟨Y1, Y2, wo, wdO, sY, hY1, hY2⟩ := hY
  have hFm : (F ++ m.drop 3).length < m.length := by
    rw [List.length_append, List.length_drop]
    omega
  refine ⟨higmanVCTau_dM m o, higmanVCTau_dO m o, F ++ m.drop 3, Y1, hN0, ?_, ?_, ?_⟩
  · exact higmanVCTauBridge_mkNode (higmanVCTauBridge_mkStep hFQ hQF (by omega) hQl wm wo)
      (by omega)
  · exact higmanVCTauBridge_mkEdge (higmanVCTauBridge_mkStep hFQ hQF (by omega) hQl wP wQ)
      hPl (by omega) (higmanVCTauBridge_mkStep hFQ hQF (by omega) hQl wdM wdO) (by omega)
  · exact higmanVCTauBridge_mkEdge (higmanVCTauBridge_mkStep hpq hqp hp hq sF sQ)
      (by omega) hQ1 (higmanVCTauBridge_mkStep hpq hqp hp hq (sF.append (m.drop 3)) sY)
      (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_core

/-- **Chains from a fresh bridge.**  A lower-level instance `s = (p, q)` at a long pair
`(x, y)` with a fresh `F` has the descent chain `(pP, pQ) — (F, pQ) — s`. -/
theorem higmanVCTauBridge_chain_of_fresh {d : ℕ} (hd : 1 < d) {p q x y x' y' F : List (Fin d)}
    (hlong : ¬ (x.length ≤ 3 ∧ y.length ≤ 3)) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hlt : x'.length + y'.length < x.length + y.length)
    (hFr : higmanVCTauBridge_Fresh d p q x y F) : higmanVCTauTight_Chain d p q x y x' y' := by
  unfold higmanVCTauTight_Chain higmanVCTauTight_Link
  refine ⟨hlong, ?_⟩
  by_cases hl : y.length ≤ x.length
  · have e1 : higmanVCTau_pP (x, y) = higmanVCTau_descP x y := if_pos hl
    have e2 : higmanVCTau_pQ (x, y) = x.take 3 := if_pos hl
    have hx4 : 4 ≤ x.length := by
      by_contra h
      exact hlong ⟨by omega, by omega⟩
    obtain ⟨hF, ⟨hFP, hPF⟩, ⟨hFQ, hQF⟩, -, ⟨hFy, hyF⟩, ⟨hFp, hpF⟩, ⟨hFq, hqF⟩⟩ := hFr
    rw [e1] at hFP hPF
    rw [e2] at hFQ hQF
    obtain ⟨X0, Y0, X1, Y1, h0, h1, h2, h3⟩ := higmanVCTauBridge_core hd hx4 hyx hpq hqp hp hq
      hmx hmy hlt hF hFP hPF hFQ hQF hFy hyF hFp hpF hFq hqF
    exact ⟨higmanVCTau_descP x y, x.take 3, X0, Y0, F, x.take 3, X1, Y1,
      Or.inl ⟨e1.symm, e2.symm⟩, h0, h1, Or.inr (Or.inr h2), Or.inr (Or.inr h3)⟩
  · have e1 : higmanVCTau_pP (x, y) = higmanVCTau_descP y x := if_neg hl
    have e2 : higmanVCTau_pQ (x, y) = y.take 3 := if_neg hl
    have hy4 : 4 ≤ y.length := by
      by_contra h
      exact hlong ⟨by omega, by omega⟩
    obtain ⟨hF, ⟨hFP, hPF⟩, ⟨hFQ, hQF⟩, ⟨hFx, hxF⟩, -, ⟨hFp, hpF⟩, ⟨hFq, hqF⟩⟩ := hFr
    rw [e1] at hFP hPF
    rw [e2] at hFQ hQF
    obtain ⟨X0, Y0, X1, Y1, h0, h1, h2, h3⟩ := higmanVCTauBridge_core hd hy4 hxy hpq hqp hp hq
      hmy hmx (by omega) hF hFP hPF hFQ hQF hFx hxF hFp hpF hFq hqF
    have h2' := higmanVCTauBridge_edge_swap h2
    have h3' := higmanVCTauBridge_edge_swap h3
    rw [Nat.add_comm y.length x.length] at h2' h3'
    exact ⟨higmanVCTau_descP y x, y.take 3, Y0, X0, F, y.take 3, Y1, X1,
      Or.inl ⟨e1.symm, e2.symm⟩, higmanVCTauBridge_node_swap h0, higmanVCTauBridge_node_swap h1,
      Or.inr (Or.inr h2'), Or.inr (Or.inr h3')⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_chain_of_fresh

end GroupApproximation.BooneHigman.Metabelian.Envelope
