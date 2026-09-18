import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBridgeReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Word helpers for the two-letter bridge residual (lane bh-met-77v)

Helpers for `higmanVCTauBridge_Residual` (`d = 2`, no fresh word):

* `higmanVCTauD2_bin`: on two letters every letter `≠ a` is `other a`;
* incomparability and fixing helpers, the images of a cone swap on prefixed words;
* `higmanVCTauD2_UV`, `higmanVCTauD2_uv_of`: a level-lowering short swap `s` is `(u v)` with
  `|u| < |v| ≤ 3`, `u` a prefix of neither word and `v` a prefix of one of them;
* `higmanVCTauD2_Good`: a bridge, a direct edge or equality with the root;
* `higmanVCTauD2_ChainMO`, `higmanVCTauD2_chainMO_of_good`: the chain in main/other form.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- On two letters every letter other than `a` is `other a`. -/
theorem higmanVCTauD2_bin {d : ℕ} (hd : d = 2) {a e : Fin d} (h : e ≠ a) :
    e = higmanVCTau_other a := by
  subst hd
  apply Fin.ext
  have h1 := a.isLt
  have h2 := e.isLt
  have h3 : e.val ≠ a.val := fun h' => h (Fin.ext h')
  show e.val = (a.val + 1) % 2
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_bin

/-- Incomparability survives a common first letter. -/
theorem higmanVCTauD2_inc_tail {d : ℕ} (e : Fin d) {W1 W2 : List (Fin d)}
    (h : ¬ W1 <+: W2 ∧ ¬ W2 <+: W1) : ¬ e :: W1 <+: e :: W2 ∧ ¬ e :: W2 <+: e :: W1 :=
  ⟨fun h' => h.1 (List.cons_prefix_cons.mp h').2,
    fun h' => h.2 (List.cons_prefix_cons.mp h').2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_inc_tail

/-- Words with equal first letters and different second letters are incomparable. -/
theorem higmanVCTauD2_inc2 {d : ℕ} {e z c : Fin d} (W1 W2 : List (Fin d)) (h : z ≠ c) :
    ¬ e :: z :: W1 <+: e :: c :: W2 ∧ ¬ e :: c :: W2 <+: e :: z :: W1 :=
  higmanVCTauD2_inc_tail e (higmanVCTauBridge_inc_cons W1 W2 h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_inc2

/-- A cone swap fixes a word incomparable with both of its words. -/
theorem higmanVCTauD2_fix {d : ℕ} {U V W : List (Fin d)} (hVW : ¬ V <+: W) (hWV : ¬ W <+: V)
    (h1 : ¬ U <+: V ∧ ¬ V <+: U) (h2 : ¬ U <+: W ∧ ¬ W <+: U) :
    MapsCone (coneSwap V W hVW hWV) U U :=
  vgen_mapsCone_coneSwap_fix hVW hWV h1.1 h1.2 h2.1 h2.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_fix

/-- The image of a word with prefix `p` under `(p q)`. -/
theorem higmanVCTauD2_img_left {d : ℕ} (hd : 1 < d) {p q z z' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z')
    (hz : p <+: z) : z' = q ++ z.drop p.length := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨r, rfl⟩ := hz
  rw [List.drop_left]
  exact MapsCone.unique h ((mapsCone_coneSwap_left hpq hqp).append r)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_img_left

/-- The image of a word with prefix `q` under `(p q)`. -/
theorem higmanVCTauD2_img_right {d : ℕ} (hd : 1 < d) {p q z z' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z')
    (hz : q <+: z) : z' = p ++ z.drop q.length := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨r, rfl⟩ := hz
  rw [List.drop_left]
  exact MapsCone.unique h ((mapsCone_coneSwap_right hpq hqp).append r)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_img_right

/-- Length of the image of a word with prefix `p` under `(p q)`. -/
theorem higmanVCTauD2_len_left {d : ℕ} (hd : 1 < d) {p q z z' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z')
    (hz : p <+: z) : z'.length + p.length = z.length + q.length := by
  have hle := hz.length_le
  rw [higmanVCTauD2_img_left hd hpq hqp h hz, List.length_append, List.length_drop]
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_len_left

/-- Length of the image of a word with prefix `q` under `(p q)`. -/
theorem higmanVCTauD2_len_right {d : ℕ} (hd : 1 < d) {p q z z' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (h : MapsCone (coneSwap p q hpq hqp) z z')
    (hz : q <+: z) : z'.length + q.length = z.length + p.length := by
  have hle := hz.length_le
  rw [higmanVCTauD2_img_right hd hpq hqp h hz, List.length_append, List.length_drop]
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_len_right

/-- A nonempty prefix of `e :: r` starts with `e`. -/
theorem higmanVCTauD2_pre1 {d : ℕ} {e : Fin d} {v r : List (Fin d)} (h : v <+: e :: r)
    (hl : 1 ≤ v.length) : ∃ v', v = e :: v' ∧ v' <+: r := by
  rcases v with _ | ⟨v0, v'⟩
  · simp only [List.length_nil] at hl <;> omega
  · obtain ⟨h1, h2⟩ := List.cons_prefix_cons.mp h
    exact ⟨v', by rw [h1], h2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_pre1

/-- A prefix of length `≥ 2` of `a :: b :: r` starts with `a b`. -/
theorem higmanVCTauD2_pre2 {d : ℕ} {a b : Fin d} {v r : List (Fin d)} (h : v <+: a :: b :: r)
    (hl : 2 ≤ v.length) : ∃ v'', v = a :: b :: v'' ∧ v'' <+: r := by
  obtain ⟨v1, rfl, h1⟩ := higmanVCTauD2_pre1 h (by omega)
  have hl' : 1 ≤ v1.length := by
    simp only [List.length_cons] at hl
    omega
  obtain ⟨v2, rfl, h2⟩ := higmanVCTauD2_pre1 h1 hl'
  exact ⟨v2, rfl, h2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_pre2

/-- A prefix of length `3` of `a :: b :: c :: r` is `[a, b, c]`. -/
theorem higmanVCTauD2_pre3 {d : ℕ} {a b c : Fin d} {v r : List (Fin d)}
    (h : v <+: a :: b :: c :: r) (hl : v.length = 3) : v = [a, b, c] := by
  obtain ⟨v2, rfl, h2⟩ := higmanVCTauD2_pre2 h (by omega)
  rcases v2 with _ | ⟨v3, v4⟩
  · simp only [List.length_cons, List.length_nil] at hl <;> omega
  · obtain ⟨h3, -⟩ := List.cons_prefix_cons.mp h2
    rcases v4 with _ | ⟨v5, v6⟩
    · rw [h3]
    · simp only [List.length_cons] at hl <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_pre3

/-- An edge whose source pair is read in the other order. -/
theorem higmanVCTauD2_edge_pswap {d n : ℕ} {P Q R S U V : List (Fin d)}
    (h : higmanVCTauTight_Edge d n P Q R S U V) : higmanVCTauTight_Edge d n P Q S R U V := by
  obtain ⟨R1, S1, E1, E2, h1, hR1, hS1, h2, hE⟩ := h
  exact higmanVCTauBridge_mkEdge (higmanVCTauBridge_step_swap h1) hS1 hR1 h2 hE

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_edge_pswap

/-- A link read with the images of both nodes in the other order. -/
theorem higmanVCTauD2_link_swap {d n : ℕ} {P Q X Y R S U V : List (Fin d)}
    (h : higmanVCTauTight_Link d n P Q X Y R S U V) :
    higmanVCTauTight_Link d n P Q Y X R S V U := by
  unfold higmanVCTauTight_Link at h ⊢
  rcases h with ⟨h1, h2, h3, h4⟩ | h | h
  · exact Or.inl ⟨h1, h2, h4, h3⟩
  · exact Or.inr (Or.inl (higmanVCTauBridge_edge_swap h))
  · exact Or.inr (Or.inr (higmanVCTauBridge_edge_swap h))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_link_swap

/-- The short swap `(u v)` (in some order) lowering `(m, o)` to `(m', o')`: `|u| < |v| ≤ 3`,
`u` a prefix of neither word, `v` a prefix of one of them, and the images. -/
def higmanVCTauD2_UV (d : ℕ) (u v m o m' o' : List (Fin d)) : Prop :=
  v.length ≤ 3 ∧ u.length < v.length ∧ ¬ u <+: m ∧ ¬ u <+: o ∧ (v <+: m ∨ v <+: o) ∧
    (v <+: m → m' = u ++ m.drop v.length) ∧ (¬ v <+: m → m' = m) ∧
    (v <+: o → o' = u ++ o.drop v.length) ∧ (¬ v <+: o → o' = o)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_UV

/-- A level-lowering short swap `(p q)` is `(u v)` in one of the two orders. -/
theorem higmanVCTauD2_uv_of {d : ℕ} (hd : 1 < d) {p q m o m' o' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hsm : MapsCone (coneSwap p q hpq hqp) m m') (hso : MapsCone (coneSwap p q hpq hqp) o o')
    (hlt : m'.length + o'.length < m.length + o.length) :
    higmanVCTauD2_UV d q p m o m' o' ∨ higmanVCTauD2_UV d p q m o m' o' := by
  have hmv := higmanVCTauBridge_moves hd hpq hqp hsm hso hlt
  rcases Nat.lt_trichotomy q.length p.length with h | h | h
  · have hqm : ¬ q <+: m := fun hz => by
      have e := higmanVCTauD2_len_right hd hpq hqp hsm hz
      rcases higmanVCTauBridge_len_cases hd hpq hqp hso with e2 | e2 | e2 <;> omega
    have hqo : ¬ q <+: o := fun hz => by
      have e := higmanVCTauD2_len_right hd hpq hqp hso hz
      rcases higmanVCTauBridge_len_cases hd hpq hqp hsm with e2 | e2 | e2 <;> omega
    have hpmo : p <+: m ∨ p <+: o := by
      rcases hmv with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr h'
      · exact absurd h' hqm
      · exact absurd h' hqo
    left
    unfold higmanVCTauD2_UV
    exact ⟨hp, h, hqm, hqo, hpmo, higmanVCTauD2_img_left hd hpq hqp hsm,
      fun h' => higmanVCTauBridge_eq_of_not hd hpq hqp hsm h' hqm,
      higmanVCTauD2_img_left hd hpq hqp hso,
      fun h' => higmanVCTauBridge_eq_of_not hd hpq hqp hso h' hqo⟩
  · exfalso
    rcases higmanVCTauBridge_len_cases hd hpq hqp hsm with e1 | e1 | e1 <;>
      rcases higmanVCTauBridge_len_cases hd hpq hqp hso with e2 | e2 | e2 <;> omega
  · have hpm : ¬ p <+: m := fun hz => by
      have e := higmanVCTauD2_len_left hd hpq hqp hsm hz
      rcases higmanVCTauBridge_len_cases hd hpq hqp hso with e2 | e2 | e2 <;> omega
    have hpo : ¬ p <+: o := fun hz => by
      have e := higmanVCTauD2_len_left hd hpq hqp hso hz
      rcases higmanVCTauBridge_len_cases hd hpq hqp hsm with e2 | e2 | e2 <;> omega
    have hqmo : q <+: m ∨ q <+: o := by
      rcases hmv with h' | h' | h' | h'
      · exact absurd h' hpm
      · exact absurd h' hpo
      · exact Or.inl h'
      · exact Or.inr h'
    right
    unfold higmanVCTauD2_UV
    exact ⟨hq, h, hpm, hpo, hqmo, higmanVCTauD2_img_right hd hpq hqp hsm,
      fun h' => higmanVCTauBridge_eq_of_not hd hpq hqp hsm hpm h',
      higmanVCTauD2_img_right hd hpq hqp hso,
      fun h' => higmanVCTauBridge_eq_of_not hd hpq hqp hso hpo h'⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_uv_of

/-- No word of length `≤ 2` is incomparable with all of `P`, `Q`, `m`, `o`, `u`, `v`. -/
def higmanVCTauD2_NF (d : ℕ) (P Q m o u v : List (Fin d)) : Prop :=
  ∀ F : List (Fin d), F.length ≤ 2 → (¬ F <+: P ∧ ¬ P <+: F) → (¬ F <+: Q ∧ ¬ Q <+: F) →
    (¬ F <+: m ∧ ¬ m <+: F) → (¬ F <+: o ∧ ¬ o <+: F) → (¬ F <+: u ∧ ¬ u <+: F) →
    (¬ F <+: v ∧ ¬ v <+: F) → False

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_NF

/-- A good position of the swap `(u v)` relative to the root `(P, Q)` at `(m, o)`: a bridge
node `(P₁, Q₁)` with edges into the root and into `(u, v)`, a direct edge from the root, or
`(u, v) = (P, Q)`. -/
def higmanVCTauD2_Good (d : ℕ) (P Q m o u v m' o' : List (Fin d)) : Prop :=
  (∃ X0 Y0 P1 Q1 X1 Y1 : List (Fin d), higmanVCTauTight_Node d m o P Q X0 Y0 ∧
      higmanVCTauTight_Node d m o P1 Q1 X1 Y1 ∧
      higmanVCTauTight_Edge d (m.length + o.length) P1 Q1 P Q X0 Y0 ∧
      higmanVCTauTight_Edge d (m.length + o.length) P1 Q1 u v m' o') ∨
    (∃ X0 Y0 : List (Fin d), higmanVCTauTight_Node d m o P Q X0 Y0 ∧
      higmanVCTauTight_Edge d (m.length + o.length) P Q u v m' o') ∨
    (u = P ∧ v = Q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_Good

/-- The descent chain in main/other form. -/
def higmanVCTauD2_ChainMO (d : ℕ) (p q m o m' o' : List (Fin d)) : Prop :=
  ∃ P0 Q0 X0 Y0 P1 Q1 X1 Y1 : List (Fin d),
    ((P0 = higmanVCTau_descP m o ∧ Q0 = m.take 3) ∨
      (P0 = m.take 3 ∧ Q0 = higmanVCTau_descP m o)) ∧
    higmanVCTauTight_Node d m o P0 Q0 X0 Y0 ∧ higmanVCTauTight_Node d m o P1 Q1 X1 Y1 ∧
    higmanVCTauTight_Link d (m.length + o.length) P0 Q0 X0 Y0 P1 Q1 X1 Y1 ∧
    higmanVCTauTight_Link d (m.length + o.length) P1 Q1 X1 Y1 p q m' o'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauD2_ChainMO
