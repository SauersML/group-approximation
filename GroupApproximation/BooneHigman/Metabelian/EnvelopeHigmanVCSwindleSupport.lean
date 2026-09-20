import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleAction
import GroupApproximation.Meta.AxiomGuard

/-!
# Unchanged cones under an elementary shuffle

A shuffle at one leaf fixes every first-letter-prefixed cone belonging to an
incomparable leaf. This is the support calculation needed for code expansion.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

theorem higSw_frame_leaf_incomp {d : ℕ} {c e : List (Fin d)}
    (hce : ¬ c <+: e) (hec : ¬ e <+: c) (u v a : Fin d) :
    (¬ [u] ++ c ++ [v] <+: [a] ++ e) ∧
      (¬ [a] ++ e <+: [u] ++ c ++ [v]) := by
  by_cases hua : u = a
  · subst u
    constructor
    · simpa only [List.cons_append, List.nil_append, List.cons_prefix_cons, true_and] using
        vgen_not_prefix_append_left [v] hce
    · simpa only [List.cons_append, List.nil_append, List.cons_prefix_cons, true_and] using
        vgen_not_prefix_append_right [v] hce hec
  · constructor
    · simpa only [List.cons_append, List.nil_append] using
        higSw_not_prefix_cons hua (c ++ [v]) e
    · simpa only [List.cons_append, List.nil_append] using
        higSw_not_prefix_cons (Ne.symm hua) e (c ++ [v])

theorem higSw_shuffle_factor_fix {d : ℕ} {c e : List (Fin d)}
    (hce : ¬ c <+: e) (hec : ¬ e <+: c)
    {p : Fin d × Fin d} (hp : p.1 < p.2) (a : Fin d) :
    MapsCone (higmanVCCommon_perm d
      (FreeGroup.of (higSw_frame c p, higSw_frame c p.swap)))
      ([a] ++ e) ([a] ++ e) := by
  have hn : p ≠ p.swap := higSw_ordered_ne_flip hp hp
  have h1 := higSw_frame_leaf_incomp hce hec p.1 p.2 a
  have h2 := higSw_frame_leaf_incomp hce hec p.2 p.1 a
  rw [higmanVCCommon_perm_of,
    vgenSwapOrOne_eq (higSw_frame_incomp c hn) (higSw_frame_incomp c hn.symm)]
  exact vgen_mapsCone_coneSwap_fix (higSw_frame_incomp c hn)
    (higSw_frame_incomp c hn.symm) h1.2 h1.1 h2.2 h2.1

theorem higSw_shuffle_list_fix {d : ℕ} {c e : List (Fin d)}
    (hce : ¬ c <+: e) (hec : ¬ e <+: c)
    (l : List (Fin d × Fin d)) (hl : ∀ p ∈ l, p.1 < p.2) (a : Fin d) :
    MapsCone (higmanVCCommon_perm d
      ((l.map fun p => FreeGroup.of (higSw_frame c p, higSw_frame c p.swap)).prod))
      ([a] ++ e) ([a] ++ e) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, higmanVCCommon_perm_one]
    exact mapsCone_one _
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, higmanVCCommon_perm_mul]
    exact (ih (fun t ht => hl t (List.mem_cons_of_mem p ht))).comp
      (higSw_shuffle_factor_fix hce hec (hl p List.mem_cons_self) a)

/-- Shuffling at an incomparable middle word leaves this entire cone unchanged. -/
theorem higSw_shuffle_fix {d : ℕ} {c e : List (Fin d)}
    (hce : ¬ c <+: e) (hec : ¬ e <+: c) (a : Fin d) :
    MapsCone (higmanVCTreeNF_E d (higSw_shuffle d c) : Equiv.Perm (Cantor (Fin d)))
      ([a] ++ e) ([a] ++ e) :=
  higSw_shuffle_list_fix hce hec (higSw_shufflePairs d)
    (fun _ hp => higSw_shufflePairs_lt hp) a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_shuffle_fix

end GroupApproximation.BooneHigman.Metabelian.Envelope
