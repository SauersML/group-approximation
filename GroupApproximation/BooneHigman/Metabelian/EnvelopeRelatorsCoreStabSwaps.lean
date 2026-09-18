import GroupApproximation.BooneHigman.Metabelian.EnvelopeRelatorsCoreStabGen
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenAll
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenFamily
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenConj
import GroupApproximation.BooneHigman.V.Transitive
import GroupApproximation.Meta.AxiomGuard

/-!
# The pointwise stabilizer of `cone [x₀]` from finitely many short cone swaps

`rnCoreShortHyp G x₀`: `G` contains the cone swaps of incomparable nonempty words of length
`≤ 4` avoiding `[x₀]`.
* `rnCore_localize_mem`: then `G` contains `localize [y] f` for every `f ∈ V_X` and `y ≠ x₀`
  (localize the short swaps of `vgen_swapIn_of_short`, then `swapGen_mem_of_coneSwap_mem`).
* `rnCore_swapHyp`: then `G` contains every cone swap of nonempty words avoiding `[x₀]`. Same
  first letter: localize. Different first letters: conjugate a swap of words of length `≤ 2` by
  a product of two localized elements (`vgen_conj_coneSwap`).
* `rnCore_stab_closure`: the finite set `rnCoreStabGens x₀` of such short swaps generates every
  element of `V_X` fixing `cone [x₀]` pointwise (`rnCore_mem_of_fix`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- Short cone swaps of nonempty words avoiding `[x₀]`, all in `G`. -/
def rnCoreShortHyp (G : Subgroup (Equiv.Perm (Cantor X))) (x₀ : X) : Prop :=
  ∀ (v w : List X) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v), v.length ≤ 4 → w.length ≤ 4 → v ≠ [] →
    ¬ [x₀] <+: v → w ≠ [] → ¬ [x₀] <+: w → coneSwap v w h1 h2 ∈ G

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCoreShortHyp

theorem rnCore_cons_incomp (y : X) {a b : List X} (h : ¬ a <+: b) : ¬ (y :: a) <+: (y :: b) :=
  fun h' => h (List.cons_prefix_cons.mp h').2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_cons_incomp

theorem rnCore_not_root_cons {x₀ y : X} (hy : y ≠ x₀) (a : List X) : ¬ [x₀] <+: y :: a :=
  fun h => hy (List.cons_prefix_cons.mp h).1.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_not_root_cons

theorem rnCore_not_prefix_cons {y : X} {a : List X} {z : Cantor X} (h : ¬ IsStreamPrefix a z) :
    ¬ IsStreamPrefix (y :: a) (prepend [y] z) := fun hc => h (by
  obtain ⟨t, ht⟩ := mem_cone_iff.mp hc
  have ht' : prepend [y] z = prepend [y] (prepend a t) := ht.trans (prepend_append [y] a t)
  exact (mem_cone_iff (w := a) (x := z)).mpr ⟨t, prepend_injective [y] ht'⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_not_prefix_cons

/-- Localizing a cone swap at a letter prepends the letter to both words. -/
theorem rnCore_localize_coneSwap (y : X) {a b : List X} (h1 : ¬ a <+: b) (h2 : ¬ b <+: a) :
    localize [y] (coneSwap a b h1 h2) =
      coneSwap (y :: a) (y :: b) (rnCore_cons_incomp y h1) (rnCore_cons_incomp y h2) := by
  refine Equiv.ext fun x => ?_
  rw [coneSwap_apply]
  by_cases hx : IsStreamPrefix [y] x
  · obtain ⟨z, rfl⟩ := mem_cone_iff.mp hx
    rw [localize_apply_prepend, coneSwap_apply]
    by_cases hza : IsStreamPrefix a z
    · obtain ⟨t, rfl⟩ := mem_cone_iff.mp hza
      rw [coneSwapFun_prepend_left, ← prepend_append, ← prepend_append, List.singleton_append,
        List.singleton_append]
      exact (coneSwapFun_prepend_left _ _ t).symm
    · by_cases hzb : IsStreamPrefix b z
      · obtain ⟨t, rfl⟩ := mem_cone_iff.mp hzb
        rw [coneSwapFun_prepend_right h1 h2, ← prepend_append, ← prepend_append,
          List.singleton_append, List.singleton_append]
        exact (coneSwapFun_prepend_right (rnCore_cons_incomp y h1) (rnCore_cons_incomp y h2)
          t).symm
      · rw [coneSwapFun_of_not hza hzb]
        exact (coneSwapFun_of_not (rnCore_not_prefix_cons (y := y) hza)
          (rnCore_not_prefix_cons (y := y) hzb)).symm
  · rw [localize_apply_of_not hx]
    have ha : ¬ IsStreamPrefix (y :: a) x := fun h =>
      hx (IsStreamPrefix.of_prefix ⟨a, List.singleton_append⟩ h)
    have hb : ¬ IsStreamPrefix (y :: b) x := fun h =>
      hx (IsStreamPrefix.of_prefix ⟨b, List.singleton_append⟩ h)
    exact (coneSwapFun_of_not ha hb).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_localize_coneSwap

theorem rnCore_localize_mapsCone (y : X) {e : Equiv.Perm (Cantor X)} {a' a : List X}
    (hm : MapsCone e a' a) : MapsCone (localize [y] e) (y :: a') (y :: a) := fun t => by
  show localize [y] e (prepend ([y] ++ a') t) = prepend ([y] ++ a) t
  rw [prepend_append, prepend_append, localize_apply_prepend, hm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_localize_mapsCone

theorem rnCore_localize_fix {y z : X} (hyz : y ≠ z) (e : Equiv.Perm (Cantor X)) (b : List X) :
    MapsCone (localize [y] e) (z :: b) (z :: b) := fun t =>
  localize_apply_of_not (fun h =>
    (prefix_or_prefix_of_isStreamPrefix h (isStreamPrefix_prepend (z :: b) t)).elim
      (fun h' => hyz (List.cons_prefix_cons.mp h').1)
      (fun h' => hyz (List.cons_prefix_cons.mp h').1.symm)) e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_localize_fix

theorem rnCore_exists_short [Finite X] [Nontrivial X] (a : List X) :
    ∃ a' : List X, a'.length ≤ 1 ∧ ∃ e ∈ higmanThompsonV X, MapsCone e a' a := by
  rcases a with _ | ⟨c, t⟩
  · exact ⟨[], by simp, 1, (higmanThompsonV X).one_mem, fun x => rfl⟩
  · obtain ⟨e, he, hm⟩ := exists_mapsCone_of_ne_nil (List.cons_ne_nil c []) (List.cons_ne_nil c t)
    exact ⟨[c], by simp, e, he, hm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_exists_short

/-- Every localized element of `V_X` at a letter `y ≠ x₀` lies in `G`. -/
theorem rnCore_localize_mem [Finite X] [Nontrivial X] {G : Subgroup (Equiv.Perm (Cantor X))}
    {x₀ : X} (hG : rnCoreShortHyp G x₀) {y : X} (hy : y ≠ x₀) {f : Equiv.Perm (Cantor X)}
    (hf : f ∈ higmanThompsonV X) : localize [y] f ∈ G := by
  have hbase : ∀ v w : List X, v.length ≤ 3 → w.length ≤ 3 →
      VGenSwapIn (G.comap (localize [y])) v w := by
    intro a b ha hb h1' h2'
    rw [Subgroup.mem_comap, rnCore_localize_coneSwap]
    exact hG (y :: a) (y :: b) (rnCore_cons_incomp y h1') (rnCore_cons_incomp y h2')
      (by rw [List.length_cons]; omega) (by rw [List.length_cons]; omega)
      (List.cons_ne_nil y a) (rnCore_not_root_cons hy a) (List.cons_ne_nil y b)
      (rnCore_not_root_cons hy b)
  exact Subgroup.mem_comap.mp
    (swapGen_mem_of_coneSwap_mem (fun v w h1 h2 => vgen_swapIn_of_short hbase v w h1 h2) hf)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_localize_mem

/-- **All avoiding cone swaps from the short ones.** -/
theorem rnCore_swapHyp [Finite X] [Nontrivial X] {G : Subgroup (Equiv.Perm (Cantor X))}
    {x₀ : X} (hG : rnCoreShortHyp G x₀) : rnCoreSwapHyp G x₀ := by
  intro v w h1 h2 hv hvx hw hwx
  obtain ⟨y, a, rfl⟩ := List.exists_cons_of_ne_nil hv
  obtain ⟨z, b, rfl⟩ := List.exists_cons_of_ne_nil hw
  have hy : y ≠ x₀ := by
    rintro rfl
    exact hvx ⟨a, List.singleton_append⟩
  by_cases hyz : y = z
  · subst hyz
    have ha : ¬ a <+: b := fun h => h1 (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
    have hb : ¬ b <+: a := fun h => h2 (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
    have hmem := rnCore_localize_mem hG hy (coneSwap_mem_higmanThompsonV ha hb)
    rw [rnCore_localize_coneSwap] at hmem
    exact hmem
  · have hz : z ≠ x₀ := by
      rintro rfl
      exact hwx ⟨b, List.singleton_append⟩
    obtain ⟨a', ha', e₁, he₁, hm₁⟩ := rnCore_exists_short a
    obtain ⟨b', hb', e₂, he₂, hm₂⟩ := rnCore_exists_short b
    have hf1 : MapsCone (localize [y] e₁ * localize [z] e₂) (y :: a') (y :: a) :=
      MapsCone.comp (rnCore_localize_fix (Ne.symm hyz) e₂ a') (rnCore_localize_mapsCone y hm₁)
    have hf2 : MapsCone (localize [y] e₁ * localize [z] e₂) (z :: b') (z :: b) :=
      MapsCone.comp (rnCore_localize_mapsCone z hm₂) (rnCore_localize_fix hyz e₁ b)
    have h1' : ¬ (y :: a') <+: (z :: b') := not_prefix_cons_of_ne hyz a' b'
    have h2' : ¬ (z :: b') <+: (y :: a') := not_prefix_cons_of_ne (Ne.symm hyz) b' a'
    have hfG : localize [y] e₁ * localize [z] e₂ ∈ G :=
      G.mul_mem (rnCore_localize_mem hG hy he₁) (rnCore_localize_mem hG hz he₂)
    rw [← vgen_conj_coneSwap h1 h2 h1' h2' hf1 hf2]
    exact G.mul_mem (G.mul_mem hfG (hG _ _ h1' h2' (by rw [List.length_cons]; omega)
      (by rw [List.length_cons]; omega) (List.cons_ne_nil y a') (rnCore_not_root_cons hy a')
      (List.cons_ne_nil z b') (rnCore_not_root_cons hz b'))) (G.inv_mem hfG)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_swapHyp

/-- The short cone swaps of nonempty words avoiding `[x₀]`, as elements of `V_X`. -/
def rnCoreStabGens [Finite X] (x₀ : X) : Set ↥(higmanThompsonV X) :=
  {s | ∃ (v w : List X) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v), v.length ≤ 4 ∧ w.length ≤ 4 ∧
    v ≠ [] ∧ ¬ [x₀] <+: v ∧ w ≠ [] ∧ ¬ [x₀] <+: w ∧
      s = ⟨coneSwap v w h1 h2, coneSwap_mem_higmanThompsonV h1 h2⟩}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCoreStabGens

theorem rnCoreStabGens_finite [Finite X] (x₀ : X) : (rnCoreStabGens x₀).Finite := by
  refine (((List.finite_length_le X 4).prod (List.finite_length_le X 4)).image
    fun p : List X × List X => vgenSwapOrOne p.1 p.2).subset ?_
  rintro s ⟨v, w, h1, h2, hv, hw, -, -, -, -, rfl⟩
  exact ⟨(v, w), ⟨hv, hw⟩, vgenSwapOrOne_eq h1 h2⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCoreStabGens_finite

theorem rnCoreStabGens_fix [Finite X] (x₀ : X) :
    ∀ f ∈ rnCoreStabGens x₀, ∀ y : Cantor X,
      (f : Equiv.Perm (Cantor X)) (prepend [x₀] y) = prepend [x₀] y := by
  rintro f ⟨v, w, h1, h2, -, -, hv, hvx, hw, hwx, rfl⟩
  exact rnCore_swap_fix h1 h2 hv hvx hw hwx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCoreStabGens_fix

/-- **The pointwise stabilizer of `cone [x₀]` is generated by `rnCoreStabGens x₀`.** -/
theorem rnCore_stab_closure [Finite X] [Nontrivial X] (x₀ : X) (f : ↥(higmanThompsonV X))
    (hf : MapsCone (f : Equiv.Perm (Cantor X)) [x₀] [x₀]) :
    f ∈ Subgroup.closure (rnCoreStabGens x₀) := by
  have hG : rnCoreShortHyp ((Subgroup.closure (rnCoreStabGens x₀)).map
      (higmanThompsonV X).subtype) x₀ := fun v w h1 h2 hvl hwl hv hvx hw hwx =>
    Subgroup.mem_map.mpr ⟨⟨coneSwap v w h1 h2, coneSwap_mem_higmanThompsonV h1 h2⟩,
      Subgroup.subset_closure ⟨v, w, h1, h2, hvl, hwl, hv, hvx, hw, hwx, rfl⟩, rfl⟩
  obtain ⟨g, hg, hgf⟩ := Subgroup.mem_map.mp (rnCore_mem_of_fix (rnCore_swapHyp hG) f.2 hf)
  have hgf' : g = f := Subtype.ext hgf
  rw [← hgf']
  exact hg

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_stab_closure

end GroupApproximation.BooneHigman.Metabelian.Envelope
