import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenLeaf
import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsCoreCones
import GroupApproximation.Meta.AxiomGuard

/-!
# The pointwise stabilizer of `cone [x₀]`: leaf permutations

`rnCoreSwapHyp G x₀`: the subgroup `G` contains every cone swap of two nonempty incomparable
words neither of which extends `[x₀]`.  Such swaps fix `cone [x₀]` pointwise
(`rnCore_swap_fix`).
* `rnCore_target_avoid`: an element fixing `cone [x₀]` pointwise carries a cone not inside
  `cone [x₀]` onto a cone not inside `cone [x₀]`.
* `rnCore_leaf`: a prefix substitution fixing `cone [x₀]` pointwise and permuting the cones of
  the words of length `N ≥ 1` lies in `G`.  This is `swapGen_leaf`, run inside the stabilizer:
  every moved word avoids `[x₀]`, and so does its image.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

variable {X : Type*}

/-- Cone swaps of nonempty words avoiding `[x₀]`, all in `G`. -/
def rnCoreSwapHyp (G : Subgroup (Equiv.Perm (Cantor X))) (x₀ : X) : Prop :=
  ∀ (v w : List X) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v), v ≠ [] → ¬ [x₀] <+: v → w ≠ [] →
    ¬ [x₀] <+: w → coneSwap v w h1 h2 ∈ G

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCoreSwapHyp

theorem rnCore_not_prefix_root {x₀ : X} {v : List X} (hv : v ≠ []) (hvx : ¬ [x₀] <+: v) :
    ¬ v <+: [x₀] := fun h => by
  rcases v with _ | ⟨c, t⟩
  · exact hv rfl
  · obtain ⟨rfl, ht⟩ := List.cons_prefix_cons.mp h
    rw [List.prefix_nil.mp ht] at hvx
    exact hvx List.prefix_rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_not_prefix_root

/-- A swap of nonempty words avoiding `[x₀]` fixes `cone [x₀]` pointwise. -/
theorem rnCore_swap_fix {x₀ : X} {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v)
    (hv : v ≠ []) (hvx : ¬ [x₀] <+: v) (hw : w ≠ []) (hwx : ¬ [x₀] <+: w) :
    MapsCone (coneSwap v w h1 h2) [x₀] [x₀] :=
  rcore_mapsCone_coneSwap_fix h1 h2 (rnCore_not_prefix_root hv hvx) hvx
    (rnCore_not_prefix_root hw hwx) hwx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_swap_fix

theorem rnCore_target_avoid [Nontrivial X] {x₀ : X} {f : Equiv.Perm (Cantor X)}
    (hfix : MapsCone f [x₀] [x₀]) {w v : List X} (hv : MapsCone f w v) (hw : ¬ [x₀] <+: w) :
    ¬ [x₀] <+: v := by
  rintro ⟨s, rfl⟩
  exact hw ⟨s, (MapsCone.unique hv.inv (hfix.append s).inv).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_target_avoid

/-- A word moved by an element fixing `cone [x₀]` pointwise does not extend `[x₀]`. -/
theorem rnCore_moved_avoid {x₀ : X} {f : Equiv.Perm (Cantor X)} (hfix : MapsCone f [x₀] [x₀])
    {w : List X} (hww : ¬ MapsCone f w w) : ¬ [x₀] <+: w := by
  rintro ⟨s, rfl⟩
  exact hww (hfix.append s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_moved_avoid

/-- **Leaf permutations in the stabilizer.** -/
theorem rnCore_leaf [Finite X] [Nontrivial X] {G : Subgroup (Equiv.Perm (Cantor X))} {x₀ : X}
    (hG : rnCoreSwapHyp G x₀) (N : ℕ) (hN : 1 ≤ N) :
    ∀ f : Equiv.Perm (Cantor X), MapsCone f [x₀] [x₀] →
      (∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ v.length = N) → f ∈ G := by
  suffices H : ∀ (n : ℕ) (f : Equiv.Perm (Cantor X)), MapsCone f [x₀] [x₀] →
      (∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ v.length = N) →
      {u : List X | u.length = N ∧ ¬ MapsCone f u u}.ncard = n → f ∈ G from
    fun f hfix hf => H _ f hfix hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hfix hf hn
    rcases Set.eq_empty_or_nonempty {u : List X | u.length = N ∧ ¬ MapsCone f u u} with hB | hB
    · have hf1 : f = 1 := by
        refine Equiv.ext fun x => ?_
        have hx : MapsCone f (firstWord N x) (firstWord N x) := by
          by_contra hnot
          exact Set.eq_empty_iff_forall_notMem.mp hB (firstWord N x) ⟨length_firstWord N x, hnot⟩
        rw [Equiv.Perm.one_apply]
        conv_lhs => rw [← prepend_firstWord N x]
        rw [hx (dropN N x), prepend_firstWord]
      rw [hf1]
      exact G.one_mem
    obtain ⟨w, hwN, hww⟩ := hB
    obtain ⟨v, hv, hvN⟩ := hf w hwN
    have hne : v ≠ w := fun h => hww (by rw [h] at hv; exact hv)
    have hvw : ¬ v <+: w := swapGen_not_prefix (by rw [hvN, hwN]) hne
    have hwv : ¬ w <+: v := swapGen_not_prefix (by rw [hvN, hwN]) (Ne.symm hne)
    have hwx : ¬ [x₀] <+: w := rnCore_moved_avoid hfix hww
    have hvx : ¬ [x₀] <+: v := rnCore_target_avoid hfix hv hwx
    have hw0 : w ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hv0 : v ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hfix' : MapsCone (coneSwap v w hvw hwv * f) [x₀] [x₀] :=
      hfix.comp (rnCore_swap_fix hvw hwv hv0 hvx hw0 hwx)
    have hsub : {u : List X | u.length = N ∧ ¬ MapsCone (coneSwap v w hvw hwv * f) u u} ⊆
        {u : List X | u.length = N ∧ ¬ MapsCone f u u} := by
      rintro u ⟨huN, hu⟩
      refine ⟨huN, fun hfu => hu ?_⟩
      have huw : u ≠ w := fun h => hww (by rw [h] at hfu; exact hfu)
      have huv : u ≠ v := fun h =>
        huw (swapGen_source_eq_of_prefix hfu hv (by rw [huN, hwN]) ⟨[], by rw [List.append_nil, h]⟩)
      exact MapsCone.comp hfu
        (swapGen_fix_same_length hvw hwv (by rw [hvN, huN]) (by rw [hwN, huN]) huv huw)
    have hwf' : MapsCone (coneSwap v w hvw hwv * f) w w :=
      MapsCone.comp hv (mapsCone_coneSwap_left hvw hwv)
    have hssub : {u : List X | u.length = N ∧ ¬ MapsCone (coneSwap v w hvw hwv * f) u u} ⊂
        {u : List X | u.length = N ∧ ¬ MapsCone f u u} :=
      (Set.ssubset_iff_of_subset hsub).mpr ⟨w, ⟨hwN, hww⟩, fun h => h.2 hwf'⟩
    have hlt := Set.ncard_lt_ncard hssub ((finite_words_length_eq N).subset fun u hu => hu.1)
    have hf' : ∀ u : List X, u.length = N →
        ∃ t, MapsCone (coneSwap v w hvw hwv * f) u t ∧ t.length = N := by
      intro u huN
      obtain ⟨t, ht, htN⟩ := hf u huN
      by_cases htv : t = v
      · rw [htv] at ht
        exact ⟨w, MapsCone.comp ht (mapsCone_coneSwap_left hvw hwv), hwN⟩
      by_cases htw : t = w
      · rw [htw] at ht
        exact ⟨v, MapsCone.comp ht (mapsCone_coneSwap_right hvw hwv), hvN⟩
      exact ⟨t, MapsCone.comp ht
        (swapGen_fix_same_length hvw hwv (by rw [hvN, htN]) (by rw [hwN, htN]) htv htw), htN⟩
    have hmem := ih _ (by rw [← hn]; exact hlt) _ hfix' hf' rfl
    have hfeq : f = coneSwap v w hvw hwv * (coneSwap v w hvw hwv * f) := by
      rw [← mul_assoc, coneSwap_mul_self, one_mul]
    rw [hfeq]
    exact G.mul_mem (hG v w hvw hwv hv0 hvx hw0 hwx) hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_leaf

end GroupApproximation.BooneHigman.Metabelian.Envelope
