import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCCommonPush
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugation on arbitrary cones in the all-swaps quotient

The push theorem initially controls only sufficiently deep cones. Splitting a swap
to that depth and reassembling removes the depth restriction: whenever the boundary
action of a word replaces the prefixes of two cones while preserving every suffix,
its class conjugates the corresponding swap exactly as prescribed by the boundary action.

This uses only the defining relations, not injectivity of the boundary action. It is
the conjugation compatibility needed when refining a tree table, and is used by the
kernel-centrality proof in `EnvelopeHigmanVCCommonCentral`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The all-swaps relations give conjugation on every pair of cones whose prefixes are
replaced with every suffix preserved, without a lower bound on their depths. -/
theorem higmanVCCommon_conj_mapsCone {d : ℕ} (hd : 1 < d)
    (g : FreeGroup (List (Fin d) × List (Fin d)))
    {x y x' y' : List (Fin d)} (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hx : MapsCone (higmanVCCommon_perm d g) x x')
    (hy : MapsCone (higmanVCCommon_perm d g) y y') :
    higmanVCCommon_mk d g * higmanVCCommon_mk d (FreeGroup.of (x, y)) *
        (higmanVCCommon_mk d g)⁻¹ = higmanVCCommon_mk d (FreeGroup.of (x', y')) := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  obtain ⟨N, hN⟩ := higmanVCCommon_push hd g
  let φ : higmanVCCommon_Q d →* higmanVCCommon_Q d :=
    (MulAut.conj (higmanVCCommon_mk d g)).toMonoidHom
  have hdeep : ∀ n : ℕ, ∀ a b a' b' : List (Fin d),
      ¬ a <+: b → ¬ b <+: a →
      MapsCone (higmanVCCommon_perm d g) a a' →
      MapsCone (higmanVCCommon_perm d g) b b' →
      N ≤ a.length + n → N ≤ b.length + n →
      φ (higmanVCCommon_mk d (higmanVCCommon_deep d n a b)) =
        higmanVCCommon_mk d (higmanVCCommon_deep d n a' b') := by
    intro n
    induction n with
    | zero =>
      intro a b a' b' hab hba ha hb hla hlb
      obtain ⟨u, v, hu, hv, _, _, he⟩ := hN a b (by omega) (by omega) hab hba
      have eu : u = a' := hu.unique ha
      have ev : v = b' := hv.unique hb
      subst u
      subst v
      simpa only [higmanVCCommon_deep_zero, φ, MulAut.conj_apply,
        MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul, map_inv] using he
    | succ n ih =>
      intro a b a' b' hab hba ha hb hla hlb
      simp only [higmanVCCommon_deep_succ, map_list_prod, List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro i _
      exact ih (a ++ [i]) (b ++ [i]) (a' ++ [i]) (b' ++ [i])
        (higmanVFP_ext_incomp hab hba i i) (higmanVFP_ext_incomp hba hab i i)
        (ha.append [i]) (hb.append [i])
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp only [List.length_append, List.length_singleton]; omega)
  have hx'y' := higmanVCCommon_incomp_image (by omega : 0 < d) hx hy hxy hyx
  have hy'x' := higmanVCCommon_incomp_image (by omega : 0 < d) hy hx hyx hxy
  have h := hdeep N x y x' y' hxy hyx hx hy (by omega) (by omega)
  rw [higmanVCCommon_mk_deep N hxy hyx,
    higmanVCCommon_mk_deep N hx'y' hy'x'] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCCommon_conj_mapsCone

end GroupApproximation.BooneHigman.Metabelian.Envelope
