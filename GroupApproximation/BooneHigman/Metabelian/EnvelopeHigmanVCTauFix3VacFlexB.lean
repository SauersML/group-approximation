import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3VacBWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Flexible B in the unequal-length case (lane bh-met-92x)

For `|p| ≠ |q|`, both `≤ 3`, an instance off the cross family, not all four words short, has
flexible B at `(x, y; x', y')`.

* `higmanVCTauFix3Vac_fbL`: `(lg u, sh v) ↦ (sh u, lg v)` with `|lg| = 3`, `|sh| ≤ 2`, through
  the cone swap `(lg z)` for a separating length-2 word `z`;
* `higmanVCTauFix3Vac_fbFF`: both words fixed, through `(t s)` with `t` the length-3 head of the
  long word and `s` the shorter of `p, q`;
* `higmanVCTauFix3Vac_pq`: the configuration `(p u, q v) ↦ (q u, p v)`;
* `higmanVCTauFix3Vac_ff`: the both-fixed configuration;
* `higmanVCTauFix3Vac_flexB`: flexible B from the hypotheses of the rest statement.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Flexible B at `(lg u, sh v; sh u, lg v)`.** -/
theorem higmanVCTauFix3Vac_fbL {d : ℕ} (hd : 1 < d) {lg sh : List (Fin d)}
    (hls : ¬ lg <+: sh) (hsl : ¬ sh <+: lg) (hlg : lg.length = 3) (hsh : sh.length ≤ 2)
    (u v : List (Fin d)) :
    higmanVCTauComm_FlexB d lg sh (lg ++ u) (sh ++ v) (sh ++ u) (lg ++ v) := by
  have h0 : sh ≠ [] := fun e => hsl (Eq.subst (motive := fun w => w <+: lg) e.symm List.nil_prefix)
  obtain ⟨z, hz2, hzl, hzs⟩ := higmanVCTauFix3Vac_pstar hd hlg h0
  have hfix := higmanVCTauD2_fix (U := sh) hzl.2 hzl.1 ⟨hsl, hls⟩ ⟨hzs.2, hzs.1⟩
  unfold higmanVCTauComm_FlexB
  refine ⟨lg, z, z ++ u, sh ++ v, z, sh, sh ++ u, z ++ v, hzl.2, hzl.1, by omega, by omega,
    (mapsCone_coneSwap_right hzl.2 hzl.1).append u, hfix.append v, ?_,
    mapsCone_coneSwap_left hzl.2 hzl.1, hfix, by omega, by omega, hfix.append u,
    (mapsCone_coneSwap_left hzl.2 hzl.1).append v, ?_⟩
  · simp only [List.length_append]
    omega
  · simp only [List.length_append]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_fbL

/-- **Flexible B with both words fixed**: `(t r, o; t r, o)` through `(t s)`. -/
theorem higmanVCTauFix3Vac_fbFF {d : ℕ} {s l m o t r : List (Fin d)} (hsl : ¬ s <+: l)
    (hls : ¬ l <+: s) (hs2 : s.length ≤ 2) (hl3 : l.length ≤ 3) (hm : m = t ++ r)
    (ht : t.length = 3) (hms : ¬ s <+: m) (hml : ¬ l <+: m) (hos : ¬ o <+: s ∧ ¬ s <+: o)
    (hom : ¬ o <+: m) : higmanVCTauComm_FlexB d s l m o m o := by
  subst hm
  have htm := List.prefix_append t r
  have hts : ¬ t <+: s := fun h => by have := h.length_le; omega
  have hst : ¬ s <+: t := fun h => hms (h.trans htm)
  have hlt : ¬ l <+: t ∧ ¬ t <+: l := by
    refine ⟨fun h => hml (h.trans htm), fun h => hml ?_⟩
    have e := h.eq_of_length (by have := h.length_le; omega)
    exact Eq.subst (motive := fun w => w <+: t ++ r) e htm
  have hlfix := higmanVCTauD2_fix (U := l) hts hst hlt ⟨hls, hsl⟩
  have hX := (mapsCone_coneSwap_right hts hst).append r
  have hD1 := (mapsCone_coneSwap_left hts hst).append r
  unfold higmanVCTauComm_FlexB
  by_cases hto : t <+: o
  · obtain ⟨w, rfl⟩ := hto
    refine ⟨t, s, s ++ r, s ++ w, t, l, s ++ r, s ++ w, hts, hst, by omega, by omega, hX,
      (mapsCone_coneSwap_right hts hst).append w, ?_, mapsCone_coneSwap_right hts hst, hlfix,
      by omega, hl3, hD1, (mapsCone_coneSwap_left hts hst).append w, ?_⟩
    · simp only [List.length_append]
      omega
    · simp only [List.length_append]
      omega
  · have hot : ¬ o <+: t ∧ ¬ t <+: o := ⟨fun h => hom (h.trans htm), hto⟩
    have hofix := higmanVCTauD2_fix (U := o) hts hst hot hos
    refine ⟨t, s, s ++ r, o, t, l, s ++ r, o, hts, hst, by omega, by omega, hX, hofix, ?_,
      mapsCone_coneSwap_right hts hst, hlfix, by omega, hl3, hD1, hofix, ?_⟩
    · simp only [List.length_append]
      omega
    · simp only [List.length_append]
      omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_fbFF

end GroupApproximation.BooneHigman.Metabelian.Envelope
