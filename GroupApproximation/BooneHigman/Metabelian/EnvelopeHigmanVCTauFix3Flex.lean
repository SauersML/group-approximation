import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauFix3Words
import GroupApproximation.Meta.AxiomGuard

/-!
# Generic flexible A options through a shorter word (lane bh-met-92l)

For a cone swap `(p q)` and a word `t` with `(p q) t = t'` short, pick a word `z` shorter than
`t`, incomparable with `t`, `p` and `q` (so fixed by `(p q)`).  The cone swap `(t z)` pulls a
moved word `t r` back to the shorter `z r`, and `(p q)` fixes `z r`.

* `higmanVCTauFix3_faL`: flexible A at `(t r, y)` with `y` fixed by `(t z)` and `(p q)`;
* `higmanVCTauFix3_faR`: flexible A at `(y, t r)`, the mirror;
* `higmanVCTauFix3_faC`: flexible A at `(t r, t s)`, both moved.

Also the wrappers `higmanVCTauFix3_knownFA1/FA2/FB1/FB2`: a flexible option on the first or
second side at level `n` gives `higmanVCTauEqTwo_Known`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Flexible A at `(t r, y)`** through the cone swap `(t z)`. -/
theorem higmanVCTauFix3_faL {d : ℕ} {p q t t' z y : List (Fin d)} (r : List (Fin d))
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (htz : ¬ t <+: z) (hzt : ¬ z <+: t)
    (ht : t.length ≤ 3) (hz : z.length < t.length)
    (hyt : ¬ y <+: t ∧ ¬ t <+: y) (hyz : ¬ y <+: z ∧ ¬ z <+: y)
    (hzp : ¬ z <+: p ∧ ¬ p <+: z) (hzq : ¬ z <+: q ∧ ¬ q <+: z)
    (htt : MapsCone (coneSwap p q hpq hqp) t t') (ht' : t'.length ≤ 3)
    (hyy : MapsCone (coneSwap p q hpq hqp) y y) :
    higmanVCTauComm_FlexA d p q (t ++ r) y hpq hqp := by
  have hzz := higmanVCTauD2_fix hpq hqp hzp hzq
  unfold higmanVCTauComm_FlexA
  refine ⟨t, z, z ++ r, y, t', z, z ++ r, y, htz, hzt, ht, by omega,
    (mapsCone_coneSwap_right htz hzt).append r, higmanVCTauD2_fix htz hzt hyt hyz, ?_, htt,
    hzz, ht', by omega, hzz.append r, hyy, ?_⟩
  · simp only [List.length_append]
    omega
  · simp only [List.length_append]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_faL

/-- **Flexible A at `(y, t r)`** through the cone swap `(t z)`. -/
theorem higmanVCTauFix3_faR {d : ℕ} {p q t t' z y : List (Fin d)} (r : List (Fin d))
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (htz : ¬ t <+: z) (hzt : ¬ z <+: t)
    (ht : t.length ≤ 3) (hz : z.length < t.length)
    (hyt : ¬ y <+: t ∧ ¬ t <+: y) (hyz : ¬ y <+: z ∧ ¬ z <+: y)
    (hzp : ¬ z <+: p ∧ ¬ p <+: z) (hzq : ¬ z <+: q ∧ ¬ q <+: z)
    (htt : MapsCone (coneSwap p q hpq hqp) t t') (ht' : t'.length ≤ 3)
    (hyy : MapsCone (coneSwap p q hpq hqp) y y) :
    higmanVCTauComm_FlexA d p q y (t ++ r) hpq hqp := by
  have hzz := higmanVCTauD2_fix hpq hqp hzp hzq
  unfold higmanVCTauComm_FlexA
  refine ⟨t, z, y, z ++ r, t', z, y, z ++ r, htz, hzt, ht, by omega,
    higmanVCTauD2_fix htz hzt hyt hyz, (mapsCone_coneSwap_right htz hzt).append r, ?_, htt,
    hzz, ht', by omega, hyy, hzz.append r, ?_⟩
  · simp only [List.length_append]
    omega
  · simp only [List.length_append]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_faR

/-- **Flexible A at `(t r, t s)`** through the cone swap `(t z)`. -/
theorem higmanVCTauFix3_faC {d : ℕ} {p q t t' z : List (Fin d)} (r s : List (Fin d))
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (htz : ¬ t <+: z) (hzt : ¬ z <+: t)
    (ht : t.length ≤ 3) (hz : z.length < t.length)
    (hzp : ¬ z <+: p ∧ ¬ p <+: z) (hzq : ¬ z <+: q ∧ ¬ q <+: z)
    (htt : MapsCone (coneSwap p q hpq hqp) t t') (ht' : t'.length ≤ 3) :
    higmanVCTauComm_FlexA d p q (t ++ r) (t ++ s) hpq hqp := by
  have hzz := higmanVCTauD2_fix hpq hqp hzp hzq
  unfold higmanVCTauComm_FlexA
  refine ⟨t, z, z ++ r, z ++ s, t', z, z ++ r, z ++ s, htz, hzt, ht, by omega,
    (mapsCone_coneSwap_right htz hzt).append r, (mapsCone_coneSwap_right htz hzt).append s, ?_,
    htt, hzz, ht', by omega, hzz.append r, hzz.append s, ?_⟩
  · simp only [List.length_append]
    omega
  · simp only [List.length_append]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_faC

/-- Flexible A on the first side gives a known instance at level `n`. -/
theorem higmanVCTauFix3_knownFA1 {d n : ℕ} {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hn : x.length + y.length = n) (hn' : x'.length + y'.length = n)
    (h : higmanVCTauComm_FlexA d p q x y hpq hqp) : higmanVCTauEqTwo_Known d n p q x y x' y' := by
  unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
  exact Or.inr (Or.inr (Or.inr ⟨hn, hn', Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hpq, hqp, h⟩))))⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_knownFA1

/-- Flexible A on the second side gives a known instance at level `n`. -/
theorem higmanVCTauFix3_knownFA2 {d n : ℕ} {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hn : x.length + y.length = n) (hn' : x'.length + y'.length = n)
    (h : higmanVCTauComm_FlexA d p q x' y' hpq hqp) :
    higmanVCTauEqTwo_Known d n p q x y x' y' := by
  unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
  exact Or.inr (Or.inr (Or.inr ⟨hn, hn', Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨hpq, hqp, h⟩))))⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_knownFA2

/-- Flexible B on the first side gives a known instance at level `n`. -/
theorem higmanVCTauFix3_knownFB1 {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (hn : x.length + y.length = n) (hn' : x'.length + y'.length = n)
    (h : higmanVCTauComm_FlexB d p q x y x' y') : higmanVCTauEqTwo_Known d n p q x y x' y' := by
  unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
  exact Or.inr (Or.inr (Or.inr ⟨hn, hn', Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_knownFB1

/-- Flexible B on the second side gives a known instance at level `n`. -/
theorem higmanVCTauFix3_knownFB2 {d n : ℕ} {p q x y x' y' : List (Fin d)}
    (hn : x.length + y.length = n) (hn' : x'.length + y'.length = n)
    (h : higmanVCTauComm_FlexB d p q x' y' x y) : higmanVCTauEqTwo_Known d n p q x y x' y' := by
  unfold higmanVCTauEqTwo_Known higmanVCTauEqTwo_Opt
  exact Or.inr (Or.inr (Or.inr ⟨hn, hn', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauFix3_knownFB2

end GroupApproximation.BooneHigman.Metabelian.Envelope
