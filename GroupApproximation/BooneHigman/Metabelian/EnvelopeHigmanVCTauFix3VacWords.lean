import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3Reduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Word lemmas for the vacuity of the rest statement (lane bh-met-92x)

* `higmanVCTauFix3Vac_img`: for `|p| = |q|`, a word `w` that is not a proper prefix of `p`
  or `q` has an image under `(p q)` of the same length;
* `higmanVCTauFix3Vac_faA`, `higmanVCTauFix3Vac_faB`: flexible A at `(t r, y)` through the
  cone swap `(t z)` with `z` shorter than `t`, where `z` need not be fixed by `(p q)`
  (`faA`: `y` incomparable with `t` and `z`; `faB`: `y = t s`);
* `higmanVCTauFix3Vac_faSwap`: flexible A is symmetric in `x ↔ y`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Equal-length image.**  For `|p| = |q|`, a word that is not a proper prefix of `p` or
`q` has an image of the same length under `(p q)`. -/
theorem higmanVCTauFix3Vac_img {d : ℕ} {p q w : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hl : p.length = q.length) (h1 : w <+: p → w = p)
    (h2 : w <+: q → w = q) :
    ∃ w' : List (Fin d), MapsCone (coneSwap p q hpq hqp) w w' ∧ w'.length = w.length := by
  by_cases hp : p <+: w
  · obtain ⟨s, rfl⟩ := hp
    refine ⟨q ++ s, (mapsCone_coneSwap_left hpq hqp).append s, ?_⟩
    simp only [List.length_append]
    omega
  by_cases hq : q <+: w
  · obtain ⟨s, rfl⟩ := hq
    refine ⟨p ++ s, (mapsCone_coneSwap_right hpq hqp).append s, ?_⟩
    simp only [List.length_append]
    omega
  refine ⟨w, higmanVCTauD2_fix hpq hqp ⟨fun h => hp ?_, hp⟩ ⟨fun h => hq ?_, hq⟩, rfl⟩
  · exact Eq.subst (motive := fun u => p <+: u) (h1 h).symm (List.prefix_refl p)
  · exact Eq.subst (motive := fun u => q <+: u) (h2 h).symm (List.prefix_refl q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_img

/-- A word of length `≥ |p|` is not a proper prefix of `p`. -/
theorem higmanVCTauFix3Vac_def_long {d : ℕ} {p w : List (Fin d)} (h : p.length ≤ w.length) :
    w <+: p → w = p := fun h' => h'.eq_of_length (by have := h'.length_le; omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_def_long

/-- **Flexible A at `(t r, y)`** through `(t z)`, with `y` incomparable with `t` and `z`. -/
theorem higmanVCTauFix3Vac_faA {d : ℕ} {p q t t' z z' y y' : List (Fin d)} (r : List (Fin d))
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (htz : ¬ t <+: z) (hzt : ¬ z <+: t)
    (ht : t.length ≤ 3) (hz : z.length < t.length)
    (hyt : ¬ y <+: t ∧ ¬ t <+: y) (hyz : ¬ y <+: z ∧ ¬ z <+: y)
    (htt : MapsCone (coneSwap p q hpq hqp) t t') (ht' : t'.length ≤ 3)
    (hzz : MapsCone (coneSwap p q hpq hqp) z z') (hz' : z'.length = z.length)
    (hyy : MapsCone (coneSwap p q hpq hqp) y y') (hy' : y'.length = y.length) :
    higmanVCTauComm_FlexA d p q (t ++ r) y hpq hqp := by
  unfold higmanVCTauComm_FlexA
  refine ⟨t, z, z ++ r, y, t', z', z' ++ r, y', htz, hzt, ht, by omega,
    (mapsCone_coneSwap_right htz hzt).append r, higmanVCTauD2_fix htz hzt hyt hyz, ?_, htt,
    hzz, ht', by omega, hzz.append r, hyy, ?_⟩
  · simp only [List.length_append]
    omega
  · simp only [List.length_append]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_faA

/-- **Flexible A at `(t r, t s)`** through `(t z)`. -/
theorem higmanVCTauFix3Vac_faB {d : ℕ} {p q t t' z z' : List (Fin d)} (r s : List (Fin d))
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (htz : ¬ t <+: z) (hzt : ¬ z <+: t)
    (ht : t.length ≤ 3) (hz : z.length < t.length)
    (htt : MapsCone (coneSwap p q hpq hqp) t t') (ht' : t'.length ≤ 3)
    (hzz : MapsCone (coneSwap p q hpq hqp) z z') (hz' : z'.length = z.length) :
    higmanVCTauComm_FlexA d p q (t ++ r) (t ++ s) hpq hqp := by
  unfold higmanVCTauComm_FlexA
  refine ⟨t, z, z ++ r, z ++ s, t', z', z' ++ r, z' ++ s, htz, hzt, ht, by omega,
    (mapsCone_coneSwap_right htz hzt).append r, (mapsCone_coneSwap_right htz hzt).append s, ?_,
    htt, hzz, ht', by omega, hzz.append r, hzz.append s, ?_⟩
  · simp only [List.length_append]
    omega
  · simp only [List.length_append]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_faB

/-- **Flexible A is symmetric in `x ↔ y`.** -/
theorem higmanVCTauFix3Vac_faSwap {d : ℕ} {p q x y : List (Fin d)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} (h : higmanVCTauComm_FlexA d p q x y hpq hqp) :
    higmanVCTauComm_FlexA d p q y x hpq hqp := by
  unfold higmanVCTauComm_FlexA at h ⊢
  obtain ⟨P, Q, X, Y, P', Q', X', Y', hPQ, hQP, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12⟩ := h
  exact ⟨P, Q, Y, X, P', Q', Y', X', hPQ, hQP, h1, h2, h4, h3, by omega, h6, h7, h8, h9, h11,
    h10, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3Vac_faSwap

end GroupApproximation.BooneHigman.Metabelian.Envelope
