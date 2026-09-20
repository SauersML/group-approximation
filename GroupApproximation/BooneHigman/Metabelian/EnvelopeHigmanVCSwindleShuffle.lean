import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleDiag
import GroupApproximation.Meta.AxiomGuard

/-!
# Explicit finite shuffles for the diagonal cloning argument

For a middle word `c`, the shuffle is the finite product of the swaps
`(a c b, b c a)` over `a < b`. Its lift is specified as a free-group word.
Conjugating by the diagonal of a cone transport replaces the middle word
exactly in the presented group, without using faithful boundary evaluation.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Each unordered pair of alphabet letters, in a fixed finite order. -/
def higSw_shufflePairs (d : ℕ) : List (Fin d × Fin d) :=
  ((List.finRange d).product (List.finRange d)).filter fun p => decide (p.1 < p.2)

/-- Membership in the shuffle list implies strict ordering of the letters. -/
theorem higSw_shufflePairs_lt {d : ℕ} {p : Fin d × Fin d}
    (hp : p ∈ higSw_shufflePairs d) : p.1 < p.2 :=
  of_decide_eq_true (List.mem_filter.mp hp).2

/-- A fixed free-group lift of the finite shuffle around `c`. -/
def higSw_shuffleWord (d : ℕ) (c : List (Fin d)) :
    FreeGroup (List (Fin d) × List (Fin d)) :=
  ((higSw_shufflePairs d).map fun p =>
    FreeGroup.of ([p.1] ++ c ++ [p.2], [p.2] ++ c ++ [p.1])).prod

/-- The prescribed shuffle in the all-swaps quotient. -/
noncomputable def higSw_shuffle (d : ℕ) (c : List (Fin d)) : higmanVCCommon_Q d :=
  higmanVCCommon_mk d (higSw_shuffleWord d c)

/-- Conjugation on cones, with the conjugator already in the presented quotient. -/
theorem higSw_conj_swap {d : ℕ} (hd : 1 < d) (q : higmanVCCommon_Q d)
    {x y x' y' : List (Fin d)} (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hx : MapsCone (higmanVCTreeNF_E d q : Equiv.Perm (Cantor (Fin d))) x x')
    (hy : MapsCone (higmanVCTreeNF_E d q : Equiv.Perm (Cantor (Fin d))) y y') :
    q * higmanVCCommon_mk d (FreeGroup.of (x, y)) * q⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of (x', y')) := by
  obtain ⟨g, rfl⟩ := higmanVCTreeNF_mk_surjective d q
  exact higmanVCCommon_conj_mapsCone hd g hxy hyx hx hy

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_conj_swap

/-- The diagonal transports one shuffle factor by changing only its middle word. -/
theorem higSw_diag_conj_shuffle_factor {d : ℕ} (hd : 1 < d)
    (q : higmanVCCommon_Q d) {c c' : List (Fin d)}
    (hc : MapsCone (higmanVCTreeNF_E d q : Equiv.Perm (Cantor (Fin d))) c c')
    {a b : Fin d} (hab : a ≠ b) :
    higSw_diag d q *
        higmanVCCommon_mk d (FreeGroup.of ([a] ++ c ++ [b], [b] ++ c ++ [a])) *
        (higSw_diag d q)⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of ([a] ++ c' ++ [b], [b] ++ c' ++ [a])) := by
  apply higSw_conj_swap hd
  · simpa only [List.cons_append, List.nil_append] using
      higSw_not_prefix_cons hab (c ++ [b]) (c ++ [a])
  · simpa only [List.cons_append, List.nil_append] using
      higSw_not_prefix_cons hab.symm (c ++ [a]) (c ++ [b])
  · exact (higSw_diag_mapsCone q hc a).append [b]
  · exact (higSw_diag_mapsCone q hc b).append [a]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_diag_conj_shuffle_factor

/-- Exact naturality of the explicitly lifted shuffle under diagonal conjugation. -/
theorem higSw_diag_conj_shuffle {d : ℕ} (hd : 1 < d)
    (q : higmanVCCommon_Q d) {c c' : List (Fin d)}
    (hc : MapsCone (higmanVCTreeNF_E d q : Equiv.Perm (Cantor (Fin d))) c c') :
    higSw_diag d q * higSw_shuffle d c * (higSw_diag d q)⁻¹ = higSw_shuffle d c' := by
  let φ : higmanVCCommon_Q d →* higmanVCCommon_Q d :=
    (MulAut.conj (higSw_diag d q)).toMonoidHom
  change φ (higmanVCCommon_mk d (higSw_shuffleWord d c)) =
    higmanVCCommon_mk d (higSw_shuffleWord d c')
  simp only [higSw_shuffleWord, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro p hp
  exact higSw_diag_conj_shuffle_factor hd q hc (ne_of_lt (higSw_shufflePairs_lt hp))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_diag_conj_shuffle

/-- Endpoints with incomparable middle words remain incomparable for all outer letters. -/
theorem higSw_shuffle_endpoint_incomp {d : ℕ} {c e : List (Fin d)}
    (hce : ¬ c <+: e) (hec : ¬ e <+: c) (a b u v : Fin d) :
    ¬ [a] ++ c ++ [b] <+: [u] ++ e ++ [v] := by
  by_cases hau : a = u
  · subst u
    simp only [List.cons_append, List.nil_append, List.cons_prefix_cons, true_and]
    exact vgen_not_prefix_append_left [b] (vgen_not_prefix_append_right [v] hec hce)
  · simpa only [List.cons_append, List.nil_append] using
      higSw_not_prefix_cons hau (c ++ [b]) (e ++ [v])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_shuffle_endpoint_incomp

/-- Factors around incomparable middle words commute in the presented group. -/
theorem higSw_shuffle_factors_commute {d : ℕ} {c e : List (Fin d)}
    (hce : ¬ c <+: e) (hec : ¬ e <+: c)
    {a b u v : Fin d} (hab : a ≠ b) (huv : u ≠ v) :
    Commute
      (higmanVCCommon_mk d (FreeGroup.of ([a] ++ c ++ [b], [b] ++ c ++ [a])))
      (higmanVCCommon_mk d (FreeGroup.of ([u] ++ e ++ [v], [v] ++ e ++ [u]))) := by
  have hxy : ¬ [a] ++ c ++ [b] <+: [b] ++ c ++ [a] := by
    simpa only [List.cons_append, List.nil_append] using
      higSw_not_prefix_cons hab (c ++ [b]) (c ++ [a])
  have hyx : ¬ [b] ++ c ++ [a] <+: [a] ++ c ++ [b] := by
    simpa only [List.cons_append, List.nil_append] using
      higSw_not_prefix_cons hab.symm (c ++ [a]) (c ++ [b])
  have huv' : ¬ [u] ++ e ++ [v] <+: [v] ++ e ++ [u] := by
    simpa only [List.cons_append, List.nil_append] using
      higSw_not_prefix_cons huv (e ++ [v]) (e ++ [u])
  have hvu : ¬ [v] ++ e ++ [u] <+: [u] ++ e ++ [v] := by
    simpa only [List.cons_append, List.nil_append] using
      higSw_not_prefix_cons huv.symm (e ++ [u]) (e ++ [v])
  have hx := vgen_mapsCone_coneSwap_fix hxy hyx
    (higSw_shuffle_endpoint_incomp hec hce u v a b)
    (higSw_shuffle_endpoint_incomp hce hec a b u v)
    (higSw_shuffle_endpoint_incomp hec hce u v b a)
    (higSw_shuffle_endpoint_incomp hce hec b a u v)
  have hy := vgen_mapsCone_coneSwap_fix hxy hyx
    (higSw_shuffle_endpoint_incomp hec hce v u a b)
    (higSw_shuffle_endpoint_incomp hce hec a b v u)
    (higSw_shuffle_endpoint_incomp hec hce v u b a)
    (higSw_shuffle_endpoint_incomp hce hec b a v u)
  have hr := higmanVCCommon_mk_rel
    (higmanVCCommon_conj_mem hxy hyx hx hy huv' hvu huv' hvu)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hr
  exact (commute_iff_eq _ _).mpr
    (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hr))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_shuffle_factors_commute

/-- Explicit shuffles around incomparable middle words commute exactly. -/
theorem higSw_shuffle_commute {d : ℕ} {c e : List (Fin d)}
    (hce : ¬ c <+: e) (hec : ¬ e <+: c) :
    Commute (higSw_shuffle d c) (higSw_shuffle d e) := by
  simp only [higSw_shuffle, higSw_shuffleWord, map_list_prod, List.map_map]
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
  exact higSw_shuffle_factors_commute hce hec
    (ne_of_lt (higSw_shufflePairs_lt hp)) (ne_of_lt (higSw_shufflePairs_lt hs))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_shuffle_commute

/-- Inserting a shuffle after an incomparable initial segment moves it to the front.
This is the ordered-product identity needed for a single leaf expansion. -/
theorem higSw_shuffle_insert {d : ℕ} (c : List (Fin d))
    (before after : List (List (Fin d)))
    (hbefore : ∀ e ∈ before, ¬ c <+: e ∧ ¬ e <+: c) :
    ((before ++ c :: after).map (higSw_shuffle d)).prod =
      higSw_shuffle d c * ((before ++ after).map (higSw_shuffle d)).prod := by
  have hc : Commute (higSw_shuffle d c) (before.map (higSw_shuffle d)).prod := by
    refine Commute.list_prod_right _ _ fun z hz => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
    exact higSw_shuffle_commute (hbefore e he).1 (hbefore e he).2
  simp only [List.map_append, List.prod_append, List.map_cons, List.prod_cons]
  rw [← mul_assoc, ← hc.eq, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_shuffle_insert

/-- A matched expansion preserves exact naturality of the lifted code shuffles. -/
theorem higSw_shuffle_expansion_naturality {d : ℕ} (hd : 1 < d)
    (q sourceLift targetLift : higmanVCCommon_Q d) {c c' : List (Fin d)}
    (hc : MapsCone (higmanVCTreeNF_E d q : Equiv.Perm (Cantor (Fin d))) c c')
    (h : targetLift * q = higSw_diag d q * sourceLift) :
    (higSw_shuffle d c' * targetLift) * q =
      higSw_diag d q * (higSw_shuffle d c * sourceLift) := by
  have hn := higSw_diag_conj_shuffle hd q hc
  have he : higSw_diag d q * higSw_shuffle d c =
      higSw_shuffle d c' * higSw_diag d q := mul_inv_eq_iff_eq_mul.mp hn
  rw [mul_assoc, h, ← mul_assoc, ← he, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_shuffle_expansion_naturality

end GroupApproximation.BooneHigman.Metabelian.Envelope
