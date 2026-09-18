import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauTightReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauConjWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Bridge words: descent-graph helpers (lane bh-met-77q)

Small combinatorial facts about the descent graph of lane bh-met-77o
(`EnvelopeHigmanVCTauTightEdge`), used to build explicit descent chains
(`higmanVCTauTight_Chain`) in `EnvelopeHigmanVCTauBridgeChain`:

* constructors and orientation swaps for `Step`, `Node`, `Edge`;
* `higmanVCTauBridge_eq_of_not`: a cone swap `(p q)` fixes every word that has neither `p`
  nor `q` as a prefix;
* `higmanVCTauBridge_len_cases`: a cone swap `(p q)` changes a length by `± (|q| - |p|)` or
  not at all;
* `higmanVCTauBridge_long`: a lower-level instance has a long pair `(x, y)`;
* `higmanVCTauBridge_s_on_Q`: a level-lowering short swap `s` carries the first three letters
  of a long word to a short word, and does not lengthen the other word;
* `higmanVCTauBridge_moves`: a level-lowering swap `(p q)` has `p` or `q` as a prefix of `x`
  or `y`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Constructor for `higmanVCTauTight_Step`. -/
theorem higmanVCTauBridge_mkStep {d : ℕ} {P Q x y X Y : List (Fin d)} (hPQ : ¬ P <+: Q)
    (hQP : ¬ Q <+: P) (hP : P.length ≤ 3) (hQ : Q.length ≤ 3)
    (hx : MapsCone (coneSwap P Q hPQ hQP) x X) (hy : MapsCone (coneSwap P Q hPQ hQP) y Y) :
    higmanVCTauTight_Step d P Q x y X Y := by
  unfold higmanVCTauTight_Step
  exact ⟨hPQ, hQP, hP, hQ, hx, hy⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_mkStep

/-- Constructor for `higmanVCTauTight_Node`. -/
theorem higmanVCTauBridge_mkNode {d : ℕ} {x y P Q X Y : List (Fin d)}
    (hS : higmanVCTauTight_Step d P Q x y X Y) (h : X.length + Y.length < x.length + y.length) :
    higmanVCTauTight_Node d x y P Q X Y := by
  unfold higmanVCTauTight_Node
  exact ⟨hS, h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_mkNode

/-- Constructor for `higmanVCTauTight_Edge`. -/
theorem higmanVCTauBridge_mkEdge {d n : ℕ} {P Q R S U V R1 S1 E1 E2 : List (Fin d)}
    (h1 : higmanVCTauTight_Step d P Q R S R1 S1) (hR1 : R1.length ≤ 3) (hS1 : S1.length ≤ 3)
    (h2 : higmanVCTauTight_Step d P Q U V E1 E2) (hE : E1.length + E2.length < n) :
    higmanVCTauTight_Edge d n P Q R S U V := by
  unfold higmanVCTauTight_Edge
  exact ⟨R1, S1, E1, E2, h1, hR1, hS1, h2, hE⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_mkEdge

/-- A step read with its two words in the other order. -/
theorem higmanVCTauBridge_step_swap {d : ℕ} {P Q x y X Y : List (Fin d)}
    (h : higmanVCTauTight_Step d P Q x y X Y) : higmanVCTauTight_Step d P Q y x Y X := by
  obtain ⟨hPQ, hQP, hP, hQ, hx, hy⟩ := h
  exact higmanVCTauBridge_mkStep hPQ hQP hP hQ hy hx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_step_swap

/-- A node read with its two words in the other order. -/
theorem higmanVCTauBridge_node_swap {d : ℕ} {x y P Q X Y : List (Fin d)}
    (h : higmanVCTauTight_Node d x y P Q X Y) : higmanVCTauTight_Node d y x P Q Y X := by
  obtain ⟨hS, hl⟩ := h
  exact higmanVCTauBridge_mkNode (higmanVCTauBridge_step_swap hS) (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_node_swap

/-- An edge whose target pair is read in the other order. -/
theorem higmanVCTauBridge_edge_swap {d n : ℕ} {P Q R S U V : List (Fin d)}
    (h : higmanVCTauTight_Edge d n P Q R S U V) : higmanVCTauTight_Edge d n P Q R S V U := by
  obtain ⟨R1, S1, E1, E2, h1, hR1, hS1, h2, hE⟩ := h
  exact higmanVCTauBridge_mkEdge h1 hR1 hS1 (higmanVCTauBridge_step_swap h2) (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_edge_swap

/-- A cone swap `(p q)` fixes a word having neither `p` nor `q` as a prefix. -/
theorem higmanVCTauBridge_eq_of_not {d : ℕ} (hd : 1 < d) {p q z z' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z')
    (h1 : ¬ p <+: z) (h2 : ¬ q <+: z) : z' = z := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h3 : ¬ z <+: p := fun h3 =>
    h1 ⟨[], by rw [List.append_nil, higmanVCTauConj_eq_of_prefix_left hpq hqp h h3]⟩
  have h4 : ¬ z <+: q := fun h4 =>
    h2 ⟨[], by rw [List.append_nil, higmanVCTauConj_eq_of_prefix_right hpq hqp h h4]⟩
  exact MapsCone.unique h (vgen_mapsCone_coneSwap_fix hpq hqp h3 h1 h4 h2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_eq_of_not

/-- A cone swap `(p q)` changes the length of a word by `± (|q| - |p|)` or not at all. -/
theorem higmanVCTauBridge_len_cases {d : ℕ} (hd : 1 < d) {p q z z' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z') :
    z'.length + p.length = z.length + q.length ∨ z'.length + q.length = z.length + p.length ∨
      z'.length = z.length := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  by_cases h1 : p <+: z
  · obtain ⟨r, rfl⟩ := h1
    have e := MapsCone.unique h ((mapsCone_coneSwap_left hpq hqp).append r)
    subst e
    left
    simp only [List.length_append]
    omega
  · by_cases h2 : q <+: z
    · obtain ⟨r, rfl⟩ := h2
      have e := MapsCone.unique h ((mapsCone_coneSwap_right hpq hqp).append r)
      subst e
      right
      left
      simp only [List.length_append]
      omega
    · right
      right
      rw [higmanVCTauBridge_eq_of_not hd hpq hqp h h1 h2]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_len_cases

/-- A level-lowering instance that is not entirely short has a long pair `(x, y)`. -/
theorem higmanVCTauBridge_long {d : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hmx : MapsCone (coneSwap p q hpq hqp) x x')
    (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hlt : x'.length + y'.length < x.length + y.length)
    (hs : ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3)) :
    ¬ (x.length ≤ 3 ∧ y.length ≤ 3) := by
  rintro ⟨hx, hy⟩
  refine hs ⟨hx, hy, ?_, ?_⟩ <;>
    rcases higmanVCTauBridge_len_cases hd hpq hqp hmx with h1 | h1 | h1 <;>
    rcases higmanVCTauBridge_len_cases hd hpq hqp hmy with h2 | h2 | h2 <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_long

/-- A level-lowering short swap `s = (p q)` carries the first three letters of a long word
`m` to a short word, and does not lengthen the other word `o`. -/
theorem higmanVCTauBridge_s_on_Q {d : ℕ} (hd : 1 < d) {p q m o m' o' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hm : 4 ≤ m.length) (hsm : MapsCone (coneSwap p q hpq hqp) m m')
    (hso : MapsCone (coneSwap p q hpq hqp) o o')
    (hlt : m'.length + o'.length < m.length + o.length) :
    (∃ Q1, MapsCone (coneSwap p q hpq hqp) (m.take 3) Q1 ∧ Q1.length ≤ 3) ∧
      o'.length ≤ o.length := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hQ3 : (m.take 3).length = 3 := List.length_take_of_le (by omega)
  have hmQ : m.take 3 ++ m.drop 3 = m := List.take_append_drop 3 m
  have ho := higmanVCTauBridge_len_cases hd hpq hqp hso
  by_cases h1 : p <+: m.take 3
  · obtain ⟨u, hu⟩ := h1
    have e1 : MapsCone (coneSwap p q hpq hqp) m (q ++ (u ++ m.drop 3)) := by
      have h := (mapsCone_coneSwap_left hpq hqp).append (u ++ m.drop 3)
      rwa [← List.append_assoc p u (m.drop 3), hu, hmQ] at h
    have e2 := congrArg List.length (MapsCone.unique hsm e1)
    have hl := congrArg List.length hu
    have e3 := (mapsCone_coneSwap_left hpq hqp).append u
    rw [hu] at e3
    simp only [List.length_append, List.length_drop] at hl e2
    refine ⟨⟨q ++ u, e3, ?_⟩, ?_⟩
    · rw [List.length_append]
      rcases ho with ho | ho | ho <;> omega
    · rcases ho with ho | ho | ho <;> omega
  · by_cases h2 : q <+: m.take 3
    · obtain ⟨u, hu⟩ := h2
      have e1 : MapsCone (coneSwap p q hpq hqp) m (p ++ (u ++ m.drop 3)) := by
        have h := (mapsCone_coneSwap_right hpq hqp).append (u ++ m.drop 3)
        rwa [← List.append_assoc q u (m.drop 3), hu, hmQ] at h
      have e2 := congrArg List.length (MapsCone.unique hsm e1)
      have hl := congrArg List.length hu
      have e3 := (mapsCone_coneSwap_right hpq hqp).append u
      rw [hu] at e3
      simp only [List.length_append, List.length_drop] at hl e2
      refine ⟨⟨p ++ u, e3, ?_⟩, ?_⟩
      · rw [List.length_append]
        rcases ho with ho | ho | ho <;> omega
      · rcases ho with ho | ho | ho <;> omega
    · have h3 : ¬ m.take 3 <+: p := fun h =>
        h1 ⟨[], by
          have hle := h.length_le
          rw [List.append_nil]
          exact (h.eq_of_length (by omega)).symm⟩
      have h4 : ¬ m.take 3 <+: q := fun h =>
        h2 ⟨[], by
          have hle := h.length_le
          rw [List.append_nil]
          exact (h.eq_of_length (by omega)).symm⟩
      have hfix := vgen_mapsCone_coneSwap_fix hpq hqp h3 h1 h4 h2
      have e := hfix.append (m.drop 3)
      rw [hmQ] at e
      have e2 := MapsCone.unique hsm e
      rw [e2] at hlt
      exact ⟨⟨m.take 3, hfix, by omega⟩, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_s_on_Q

/-- A level-lowering swap `(p q)` has `p` or `q` as a prefix of `x` or of `y`. -/
theorem higmanVCTauBridge_moves {d : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hmx : MapsCone (coneSwap p q hpq hqp) x x')
    (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hlt : x'.length + y'.length < x.length + y.length) :
    p <+: x ∨ p <+: y ∨ q <+: x ∨ q <+: y := by
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨a1, a2, a3, a4⟩ := hc
  have e1 := higmanVCTauBridge_eq_of_not hd hpq hqp hmx a1 a3
  have e2 := higmanVCTauBridge_eq_of_not hd hpq hqp hmy a2 a4
  rw [e1, e2] at hlt
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBridge_moves

end GroupApproximation.BooneHigman.Metabelian.Envelope
