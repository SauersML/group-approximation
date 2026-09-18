import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenCount
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenConj
import GroupApproximation.Meta.AxiomGuard

/-!
# Leaf permutations are products of cone swaps

A prefix substitution carrying the words of length `N` onto words of length `N` permutes the
cones of the words of length `N`.  Such an element lies in every subgroup containing all cone
swaps: compose with the cone swap exchanging a moved word with its image, which strictly shrinks
the finite set of moved words (`swapGen_leaf`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- Distinct words of the same length are incomparable. -/
theorem swapGen_not_prefix {a b : List X} (hlen : a.length = b.length) (hne : a ≠ b) :
    ¬ a <+: b :=
  fun h => hne (h.eq_of_length hlen)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_not_prefix

/-- A cone swap of two words of length `|u|` fixes the cone of every other word `u`. -/
theorem swapGen_fix_same_length {v w u : List X} (hvw : ¬ v <+: w) (hwv : ¬ w <+: v)
    (hv : v.length = u.length) (hw : w.length = u.length) (huv : u ≠ v) (huw : u ≠ w) :
    MapsCone (coneSwap v w hvw hwv) u u :=
  vgen_mapsCone_coneSwap_fix hvw hwv (swapGen_not_prefix hv.symm huv)
    (swapGen_not_prefix hv (Ne.symm huv)) (swapGen_not_prefix hw.symm huw)
    (swapGen_not_prefix hw (Ne.symm huw))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_fix_same_length

/-- **Leaf permutations.** A prefix substitution carrying every word of length `N` onto a word of
length `N` lies in every subgroup containing all cone swaps. -/
theorem swapGen_leaf [Finite X] [Nontrivial X] {G : Subgroup (Equiv.Perm (Cantor X))}
    (hG : ∀ (v w : List X) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v), coneSwap v w h1 h2 ∈ G) (N : ℕ) :
    ∀ f : Equiv.Perm (Cantor X),
      (∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ v.length = N) → f ∈ G := by
  suffices H : ∀ (n : ℕ) (f : Equiv.Perm (Cantor X)),
      (∀ w : List X, w.length = N → ∃ v, MapsCone f w v ∧ v.length = N) →
      {u : List X | u.length = N ∧ ¬ MapsCone f u u}.ncard = n → f ∈ G from
    fun f hf => H _ f hf rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hn
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
    have hmem := ih _ (by rw [← hn]; exact hlt) _ hf' rfl
    have hfeq : f = coneSwap v w hvw hwv * (coneSwap v w hvw hwv * f) := by
      rw [← mul_assoc, coneSwap_mul_self, one_mul]
    rw [hfeq]
    exact G.mul_mem (hG v w hvw hwv) hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_leaf

end GroupApproximation.BooneHigman.Metabelian.Envelope
