import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3VacWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Family recognition for the vacuity of the rest statement (lane bh-met-92x)

When a candidate length-2 word `[z0, z1]` is a proper prefix of `p` or `q`, that word has the
form `[z0, z1, c]`.  From such shapes the instance lies in the both-fixed or one-fixed family.

* `higmanVCTauFix3Vac_notDef`: a failed candidate gives `p` or `q` of the form `[z0, z1, c]`;
* `higmanVCTauFix3Vac_bfSwap`: the both-fixed family is symmetric in `p ↔ q`;
* `higmanVCTauFix3Vac_bfHead`, `higmanVCTauFix3Vac_bf2`: explicit both-fixed instances;
* `higmanVCTauFix3Vac_single`: the `y = [e]` shape is both-fixed or one-fixed.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A proper extension of `[z0, z1]` of length `≤ 3` is `[z0, z1, c]`. -/
theorem higmanVCTauFix3Vac_fail2 {d : ℕ} {z0 z1 : Fin d} {p : List (Fin d)}
    (hp : p.length ≤ 3) (h : [z0, z1] <+: p) (hne : [z0, z1] ≠ p) : ∃ c, p = [z0, z1, c] := by
  obtain ⟨u, rfl⟩ := h
  rcases u with _ | ⟨c, _ | ⟨c', u⟩⟩
  · exact absurd (List.append_nil _).symm hne
  · exact ⟨c, rfl⟩
  · simp only [List.length_append, List.length_cons, List.length_nil] at hp <;> omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_fail2

/-- **A failed candidate.**  If `[z0, z1]` is a proper prefix of `p` or of `q`, then `p` or
`q` is `[z0, z1, c]`. -/
theorem higmanVCTauFix3Vac_notDef {d : ℕ} {z0 z1 : Fin d} {p q : List (Fin d)}
    (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (h : ¬ (([z0, z1] <+: p → [z0, z1] = p) ∧ ([z0, z1] <+: q → [z0, z1] = q))) :
    (∃ c, p = [z0, z1, c]) ∨ (∃ c, q = [z0, z1, c]) := by
  by_cases h1 : [z0, z1] <+: p ∧ [z0, z1] ≠ p
  · exact Or.inl (higmanVCTauFix3Vac_fail2 hp h1.1 h1.2)
  by_cases h2 : [z0, z1] <+: q ∧ [z0, z1] ≠ q
  · exact Or.inr (higmanVCTauFix3Vac_fail2 hq h2.1 h2.2)
  exact (h ⟨fun a => Classical.byContradiction fun b => h1 ⟨a, b⟩,
    fun a => Classical.byContradiction fun b => h2 ⟨a, b⟩⟩).elim

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_notDef

/-- The both-fixed family is symmetric in `p ↔ q`. -/
theorem higmanVCTauFix3Vac_bfSwap {d : ℕ} {p q x y : List (Fin d)}
    (h : higmanVCTauFix3_BothFixed p q x y) : higmanVCTauFix3_BothFixed q p x y := by
  unfold higmanVCTauFix3_BothFixed at h ⊢
  exact ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_bfSwap

/-- Both-fixed when `x, y` start with `e` and `p, q` are length 3 not starting with `e`. -/
theorem higmanVCTauFix3Vac_bfHead {d : ℕ} {p q : List (Fin d)} {e a b c a' b' c' : Fin d}
    (u v : List (Fin d)) (hp : p = [a, b, c]) (hq : q = [a', b', c']) (ha : e ≠ a)
    (ha' : e ≠ a') : higmanVCTauFix3_BothFixed p q (e :: u) (e :: v) := by
  subst hp hq
  unfold higmanVCTauFix3_BothFixed
  exact ⟨rfl, rfl, higmanVCTauBridge_inc_cons u [b, c] ha,
    higmanVCTauBridge_inc_cons u [b', c'] ha', higmanVCTauBridge_inc_cons v [b, c] ha,
    higmanVCTauBridge_inc_cons v [b', c'] ha'⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_bfHead

/-- Both-fixed for `p = [m0, m1*, c]`, `q = [e, y1*, c']` (`*` the other letter). -/
theorem higmanVCTauFix3Vac_bf2 {d : ℕ} (hd : 1 < d) {m0 m1 m2 e y1 c c' : Fin d}
    (r ys : List (Fin d)) (he : e ≠ m0) :
    higmanVCTauFix3_BothFixed [m0, higmanVCTau_other m1, c] [e, higmanVCTau_other y1, c']
      (m0 :: m1 :: m2 :: r) (e :: y1 :: ys) := by
  have ho := higmanVCTauSplit_other_ne hd
  unfold higmanVCTauFix3_BothFixed
  exact ⟨rfl, rfl, higmanVCTauD2_inc2 (m2 :: r) [c] (ho m1).symm,
    higmanVCTauBridge_inc_cons (m1 :: m2 :: r) [higmanVCTau_other y1, c'] he.symm,
    higmanVCTauBridge_inc_cons (y1 :: ys) [higmanVCTau_other m1, c] he,
    higmanVCTauD2_inc2 ys [c'] (ho y1).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_bf2

/-- **The single-letter shape.**  For `W = [m0, m1*, c]`, `|V| = 3`, `¬ [e] <+: V` and
`e ≠ m0`, the instance `(m0 m1 m2 r, [e])` is both-fixed for `(W, V)` or one-fixed for
`(V, W)`. -/
theorem higmanVCTauFix3Vac_single {d : ℕ} (hd : 1 < d) {V W : List (Fin d)}
    {m0 m1 m2 e c : Fin d} (r : List (Fin d)) (hW : W = [m0, higmanVCTau_other m1, c])
    (hV : V.length = 3) (hVy : ¬ [e] <+: V) (he : e ≠ m0) :
    higmanVCTauFix3_BothFixed W V (m0 :: m1 :: m2 :: r) [e] ∨
      higmanVCTauRest_OneFixed V W (m0 :: m1 :: m2 :: r) [e] := by
  have ho := higmanVCTauSplit_other_ne hd
  subst hW
  rcases V with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, V⟩⟩⟩⟩
  · simp only [List.length_nil] at hV <;> omega
  · simp only [List.length_cons, List.length_nil] at hV <;> omega
  · simp only [List.length_cons, List.length_nil] at hV <;> omega
  swap
  · simp only [List.length_cons] at hV <;> omega
  by_cases hx : ¬ m0 :: m1 :: m2 :: r <+: [v0, v1, v2] ∧ ¬ [v0, v1, v2] <+: m0 :: m1 :: m2 :: r
  · left
    unfold higmanVCTauFix3_BothFixed
    exact ⟨rfl, rfl, higmanVCTauD2_inc2 (m2 :: r) [c] (ho m1).symm, hx,
      higmanVCTauBridge_inc_cons [] [higmanVCTau_other m1, c] he,
      higmanVCTauFix3_incHead [] (List.cons_ne_nil _ _) hVy⟩
  right
  have hpre : [v0, v1, v2] <+: m0 :: m1 :: m2 :: r := by
    by_contra hn
    refine hx ⟨fun h => hn ?_, hn⟩
    have hlen : (m0 :: m1 :: m2 :: r).length = [v0, v1, v2].length := by
      have := h.length_le
      simp only [List.length_cons, List.length_nil] at this ⊢
      omega
    exact Eq.subst (motive := fun u => [v0, v1, v2] <+: u) (h.eq_of_length hlen).symm
      (List.prefix_refl _)
  obtain ⟨h0, h1'⟩ := List.cons_prefix_cons.mp hpre
  obtain ⟨h1, h2'⟩ := List.cons_prefix_cons.mp h1'
  obtain ⟨h2, -⟩ := List.cons_prefix_cons.mp h2'
  rw [h0, h1, h2]
  unfold higmanVCTauRest_OneFixed
  exact ⟨m0, m1, higmanVCTau_other m1, m2, c, e, r, (ho m1).symm, he, rfl, rfl,
    Or.inl ⟨rfl, rfl⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_single

end GroupApproximation.BooneHigman.Metabelian.Envelope
