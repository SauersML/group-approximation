import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCSwindleShuffle
import GroupApproximation.Meta.AxiomGuard

/-!
# Boundary action of the finite shuffle

The explicitly lifted shuffle interchanges the two outer letters around its
middle word. The proof computes its finite product of disjoint transpositions;
it does not infer equality in the presented group from a boundary calculation.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A middle word framed by the two letters of a pair. -/
def higSw_frame {d : ℕ} (c : List (Fin d)) (p : Fin d × Fin d) : List (Fin d) :=
  [p.1] ++ c ++ [p.2]

theorem higSw_frame_injective {d : ℕ} (c : List (Fin d)) :
    Function.Injective (higSw_frame c) := by
  intro p s h
  rcases p with ⟨a, b⟩
  rcases s with ⟨u, v⟩
  simpa [higSw_frame] using h

theorem higSw_frame_incomp {d : ℕ} (c : List (Fin d))
    {p s : Fin d × Fin d} (hps : p ≠ s) : ¬ higSw_frame c p <+: higSw_frame c s := by
  intro h
  apply hps
  apply higSw_frame_injective c
  exact h.eq_of_length (by simp [higSw_frame])

/-- Increasing pairs cannot be reversals of each other. -/
theorem higSw_ordered_ne_flip {d : ℕ} {p s : Fin d × Fin d}
    (hp : p.1 < p.2) (hs : s.1 < s.2) : p ≠ s.swap := by
  intro h
  have h1 : p.1 = s.2 := congrArg Prod.fst h
  have h2 : p.2 = s.1 := congrArg Prod.snd h
  rw [h1, h2] at hp
  exact lt_asymm hp hs

/-- A product of transpositions fixes a point if every factor fixes it. -/
theorem higSw_pair_prod_fix {d : ℕ} (l : List (Fin d × Fin d)) (s : Fin d × Fin d)
    (hs : ∀ p ∈ l, s ≠ p ∧ s ≠ p.swap) :
    ((l.map fun p => Equiv.swap p p.swap).prod) s = s := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    rw [ih (fun t ht => hs t (List.mem_cons_of_mem p ht))]
    exact Equiv.swap_apply_of_ne_of_ne (hs p (List.mem_cons_self)).1
      (hs p (List.mem_cons_self)).2

/-- The unique transposition at an increasing pair exchanges that pair and its reverse. -/
theorem higSw_pair_prod_hit {d : ℕ} (l : List (Fin d × Fin d)) (hl : l.Nodup)
    (ho : ∀ s ∈ l, s.1 < s.2) {p : Fin d × Fin d} (hp : p ∈ l) :
    ((l.map fun s => Equiv.swap s s.swap).prod) p = p.swap ∧
      ((l.map fun s => Equiv.swap s s.swap).prod) p.swap = p := by
  induction l with
  | nil => simp at hp
  | cons s l ih =>
    have hn := List.nodup_cons.mp hl
    have hs := ho s List.mem_cons_self
    have hol : ∀ t ∈ l, t.1 < t.2 := fun t ht => ho t (List.mem_cons_of_mem s ht)
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    rcases List.mem_cons.mp hp with hps | hpl
    · subst p
      have hfix : ∀ t ∈ l, s ≠ t ∧ s ≠ t.swap := by
        intro t ht
        exact ⟨fun e => hn.1 (e.symm ▸ ht), higSw_ordered_ne_flip hs (hol t ht)⟩
      have hfix' : ∀ t ∈ l, s.swap ≠ t ∧ s.swap ≠ t.swap := by
        intro t ht
        refine ⟨(higSw_ordered_ne_flip (hol t ht) hs).symm, ?_⟩
        intro e
        exact (hfix t ht).1 (by simpa using congrArg Prod.swap e)
      rw [higSw_pair_prod_fix l s hfix, higSw_pair_prod_fix l s.swap hfix']
      exact ⟨Equiv.swap_apply_left _ _, Equiv.swap_apply_right _ _⟩
    · have hpord := hol p hpl
      have hps : p ≠ s := fun e => hn.1 (e ▸ hpl)
      obtain ⟨ih1, ih2⟩ := ih hn.2 hol hpl
      rw [ih1, ih2]
      constructor
      · apply Equiv.swap_apply_of_ne_of_ne
        · exact (higSw_ordered_ne_flip hs hpord).symm
        · intro e
          exact hps (by simpa using congrArg Prod.swap e)
      · exact Equiv.swap_apply_of_ne_of_ne hps (higSw_ordered_ne_flip hpord hs)

theorem higSw_shufflePairs_mem {d : ℕ} {p : Fin d × Fin d} (hp : p.1 < p.2) :
    p ∈ higSw_shufflePairs d := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_product.mpr ⟨List.mem_finRange p.1, List.mem_finRange p.2⟩,
    decide_eq_true hp⟩

theorem higSw_shufflePairs_nodup (d : ℕ) : (higSw_shufflePairs d).Nodup := by
  apply List.Nodup.filter
  exact (List.nodup_finRange d).product (List.nodup_finRange d)

/-- The finite permutation of framed pairs is exactly reversal. -/
theorem higSw_pair_prod_flip {d : ℕ} (p : Fin d × Fin d) :
    (((higSw_shufflePairs d).map fun s => Equiv.swap s s.swap).prod) p = p.swap := by
  rcases lt_trichotomy p.1 p.2 with hp | hp | hp
  · exact (higSw_pair_prod_hit _ (higSw_shufflePairs_nodup d)
      (fun _ h => higSw_shufflePairs_lt h) (higSw_shufflePairs_mem hp)).1
  · have hself : p.swap = p := by ext <;> simp [hp]
    rw [hself]
    apply higSw_pair_prod_fix
    intro s hs
    have hlt := higSw_shufflePairs_lt hs
    constructor
    · intro e
      have : s.1 = s.2 := e ▸ hp
      exact (ne_of_lt hlt) this
    · intro e
      have hpe : p.1 = p.2 := hp
      rw [e] at hpe
      have : s.2 = s.1 := hpe
      exact (ne_of_lt hlt) this.symm
  · have h := (higSw_pair_prod_hit _ (higSw_shufflePairs_nodup d)
      (fun _ h => higSw_shufflePairs_lt h) (p := p.swap) (higSw_shufflePairs_mem hp)).2
    simpa using h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_pair_prod_flip

/-- Each generating cone swap acts on framed pairs as the corresponding transposition. -/
theorem higSw_shuffle_factor_mapsCone {d : ℕ} (c : List (Fin d))
    {p : Fin d × Fin d} (hp : p.1 < p.2) (s : Fin d × Fin d) :
    MapsCone (higmanVCCommon_perm d
      (FreeGroup.of (higSw_frame c p, higSw_frame c p.swap)))
      (higSw_frame c s) (higSw_frame c (Equiv.swap p p.swap s)) := by
  have hn : p ≠ p.swap := higSw_ordered_ne_flip hp hp
  rw [higmanVCCommon_perm_of,
    vgenSwapOrOne_eq (higSw_frame_incomp c hn) (higSw_frame_incomp c hn.symm)]
  by_cases hsp : s = p
  · subst s
    rw [Equiv.swap_apply_left]
    exact mapsCone_coneSwap_left (higSw_frame_incomp c hn) (higSw_frame_incomp c hn.symm)
  by_cases hsp' : s = p.swap
  · subst s
    rw [Equiv.swap_apply_right]
    exact mapsCone_coneSwap_right (higSw_frame_incomp c hn) (higSw_frame_incomp c hn.symm)
  rw [Equiv.swap_apply_of_ne_of_ne hsp hsp']
  exact vgen_mapsCone_coneSwap_fix (higSw_frame_incomp c hn) (higSw_frame_incomp c hn.symm)
    (higSw_frame_incomp c hsp) (higSw_frame_incomp c (Ne.symm hsp))
    (higSw_frame_incomp c hsp') (higSw_frame_incomp c (Ne.symm hsp'))

/-- Cone tracking through any ordered-pair list. -/
theorem higSw_shuffle_list_mapsCone {d : ℕ} (c : List (Fin d))
    (l : List (Fin d × Fin d)) (hl : ∀ p ∈ l, p.1 < p.2) (s : Fin d × Fin d) :
    MapsCone (higmanVCCommon_perm d
      ((l.map fun p => FreeGroup.of (higSw_frame c p, higSw_frame c p.swap)).prod))
      (higSw_frame c s)
      (higSw_frame c (((l.map fun p => Equiv.swap p p.swap).prod) s)) := by
  induction l generalizing s with
  | nil =>
    simp only [List.map_nil, List.prod_nil, higmanVCCommon_perm_one, Equiv.Perm.one_apply]
    exact mapsCone_one _
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, higmanVCCommon_perm_mul, Equiv.Perm.mul_apply]
    exact (ih (fun t ht => hl t (List.mem_cons_of_mem p ht)) s).comp
      (higSw_shuffle_factor_mapsCone c (hl p List.mem_cons_self) _)

/-- The explicit shuffle sends `a c b ξ` to `b c a ξ`, including the diagonal case. -/
theorem higSw_shuffle_mapsCone {d : ℕ} (c : List (Fin d)) (a b : Fin d) :
    MapsCone (higmanVCTreeNF_E d (higSw_shuffle d c) : Equiv.Perm (Cantor (Fin d)))
      ([a] ++ c ++ [b]) ([b] ++ c ++ [a]) := by
  have h := higSw_shuffle_list_mapsCone c (higSw_shufflePairs d)
    (fun _ hp => higSw_shufflePairs_lt hp) (a, b)
  rw [higSw_pair_prod_flip] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higSw_shuffle_mapsCone

end GroupApproximation.BooneHigman.Metabelian.Envelope
