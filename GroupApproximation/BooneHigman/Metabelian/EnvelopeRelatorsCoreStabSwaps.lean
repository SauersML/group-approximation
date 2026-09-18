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
        exact (coneSwapFun_prepend_right _ _ t).symm
      · rw [coneSwapFun_of_not hza hzb]
        exact (coneSwapFun_of_not (rnCore_not_prefix_cons hza)
          (rnCore_not_prefix_cons hzb)).symm
  · rw [localize_apply_of_not hx]
    exact (coneSwapFun_of_not (fun h => hx (IsStreamPrefix.of_prefix ⟨a, rfl⟩ h))
      (fun h => hx (IsStreamPrefix.of_prefix ⟨b, rfl⟩ h))).symm

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
  refine Subgroup.mem_comap.mp (swapGen_mem_of_coneSwap_mem (G := G.comap (localize [y]))
    (fun v w h1 h2 => vgen_swapIn_of_short ?_ v w h1 h2) hf)
  intro a b ha hb h1' h2'
  rw [Subgroup.mem_comap, rnCore_localize_coneSwap]
  exact hG _ _ _ _ (by rw [List.length_cons]; omega) (by rw [List.length_cons]; omega)
    (List.cons_ne_nil y a) (rnCore_not_root_cons hy a) (List.cons_ne_nil y b)
    (rnCore_not_root_cons hy b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCore_localize_mem

end GroupApproximation.BooneHigman.Metabelian.Envelope
