import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauLevelHop
import GroupApproximation.Meta.AxiomGuard

/-!
# Legs and conjugation-by-product identities for the deep hop (lane bh-met-77t)

A **leg** (`higmanVCTauDeep_Leg`) is an instance `(s; A → B)` at level `n` that the lane
bh-met-77r case lemmas already prove from the level-`n` hypotheses: it is easy, or Hop A applies
(from `A` at level `n`, or from `B` at level `n` read backwards), or Hop C applies.
`higmanVCTauDeep_leg` proves every leg; it takes the same arguments as
`higmanVCTauLevel_easy`.

The group lemmas are the algebra of the deep hop (`EnvelopeHigmanVCTauDeepHop`): if
`g = ∏_b f b` and every factor `f b` with `b ≠ a` commutes with `T` and with `f a`, then
`g T g⁻¹ = f a · T · (f a)⁻¹` (`higmanVCTauDeep_prod_conj`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Leg**: an instance proved by the existing level-`n` cases (easy, Hop A either way, Hop C). -/
def higmanVCTauDeep_Leg (d n : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  higmanVCTauLevel_Easy d n p q x y x' y' ∨
    (x.length + y.length = n ∧ ∃ (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      higmanVCTauLevel_HopA d n p q x y x' y' hpq hqp) ∨
    (x'.length + y'.length = n ∧ ∃ (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      higmanVCTauLevel_HopA d n p q x' y' x y hpq hqp) ∨
    higmanVCTauLevel_HopC d n p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_Leg

/-- **Legs are proved** from the level-`n` hypotheses. -/
theorem higmanVCTauDeep_leg {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x')
    (hL : higmanVCTauDeep_Leg d n p q x y x' y') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  rcases hL with hE | ⟨hA, _, _, hH⟩ | ⟨hA', _, _, hH⟩ | hH
  · exact higmanVCTauLevel_easy hd hB hS hpq hqp hp hq hmx hmy hxy hyx hxy' hyx' hE
  · exact higmanVCTauLevel_hopA_case hd hB hS hpq hqp hp hq hA hH hmx hmy hxy hyx hxy' hyx'
  · have hss := coneSwap_mul_self hpq hqp
    exact higmanVCTauComm_flip_eq hp hq (higmanVCTauLevel_hopA_case hd hB hS hpq hqp hp hq hA'
      hH (higmanVCTauConj_mapsCone_symm hmx hss) (higmanVCTauConj_mapsCone_symm hmy hss) hxy'
      hyx' hxy hyx)
  · exact higmanVCTauLevel_hopC_case hd hB hS hpq hqp hp hq hH hmx hmy hxy hyx hxy' hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_leg

/-- An element commuting with `T` conjugates it to itself. -/
theorem higmanVCTauDeep_conj_of_commute {G : Type*} [Group G] {g T : G} (h : Commute g T) :
    g * T * g⁻¹ = T := by
  rw [h.eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_conj_of_commute

/-- An element conjugating `T` to itself commutes with it. -/
theorem higmanVCTauDeep_commute_of_conj {G : Type*} [Group G] {g T : G} (h : g * T * g⁻¹ = T) :
    Commute g T := by
  show g * T = T * g
  exact mul_inv_eq_iff_eq_mul.mp h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_commute_of_conj

/-- Conjugation by a product is iterated conjugation. -/
theorem higmanVCTauDeep_conj_mul {G : Type*} [Group G] (g h T : G) :
    g * h * T * (g * h)⁻¹ = g * (h * T * h⁻¹) * g⁻¹ := by
  simp only [mul_inv_rev, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_conj_mul

/-- **Conjugation by a product with commuting side factors.**  If `a` occurs once in `l` and
every other factor `f b` commutes with `T` and with `f a`, then conjugating `T` by the product
`∏_{b ∈ l} f b` is conjugating it by `f a` alone. -/
theorem higmanVCTauDeep_prod_conj {G ι : Type*} [Group G] (f : ι → G) (T : G) (a : ι) :
    ∀ l : List ι, l.Nodup → a ∈ l →
      (∀ b ∈ l, b ≠ a → Commute (f b) T ∧ Commute (f b) (f a)) →
      (l.map f).prod * T * ((l.map f).prod)⁻¹ = f a * T * (f a)⁻¹ := by
  intro l
  induction l with
  | nil =>
    intro _ ha _
    simp at ha
  | cons b l ih =>
    intro hnd ha hc
    have hnd' := List.nodup_cons.mp hnd
    rw [List.map_cons, List.prod_cons, higmanVCTauDeep_conj_mul]
    by_cases hba : b = a
    · have hcomm : Commute (l.map f).prod T := by
        refine Commute.list_prod_left _ _ (fun z hz => ?_)
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hz
        have hca : c ≠ a := fun h => hnd'.1 (by rw [hba, ← h]; exact hc')
        exact (hc c (List.mem_cons_of_mem _ hc') hca).1
      rw [higmanVCTauDeep_conj_of_commute hcomm, hba]
    · have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hba
        · exact h
      rw [ih hnd'.2 ha' (fun c hc' hca => hc c (List.mem_cons_of_mem _ hc') hca)]
      obtain ⟨h1, h2⟩ := hc b (List.mem_cons.mpr (Or.inl rfl)) hba
      exact higmanVCTauDeep_conj_of_commute ((h2.mul_right h1).mul_right h2.inv_right)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauDeep_prod_conj

end GroupApproximation.BooneHigman.Metabelian.Envelope
