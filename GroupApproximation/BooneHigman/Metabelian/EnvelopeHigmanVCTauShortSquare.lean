import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauShortBase
import GroupApproximation.Meta.AxiomGuard

/-!
# Two squares for short-conjugator instances (lane bh-met-77j)

Let `s := (p, q)` be a short conjugator and `A := (x, y)` a long incomparable pair with
canonical descent `t := (P, Q)`, `C := (X, Y)`, so `τ A = ℓ_t · τ C · ℓ_t⁻¹`
(`higmanVCTauConj_tau_descent`) and `(P Q)` carries `X ↦ x`, `Y ↦ y`.

* **Option E** (`higmanVCTauShort_OptionE`, `higmanVCTauShort_optionE`): `s = t`.  Then
  `(P Q)` carries `x ↦ X`, `y ↦ Y`, so the instance is the descent identity itself.
* **Option A** (`higmanVCTauShort_OptionA`, `higmanVCTauShort_square`): `(p q)` carries
  `P ↦ P'`, `Q ↦ Q'` with `P'`, `Q'` short, and `X ↦ X'`, `Y ↦ Y'` with
  `|X'| + |Y'| < |x| + |y|`.  With `v := (P', Q')`, the all-short relator gives
  `ℓ_s ℓ_t ℓ_s⁻¹ = ℓ_v`, and `(P' Q') = (p q) (P Q) (p q)⁻¹` (`vgen_conj_coneSwap`) carries
  `X' ↦ x'`, `Y' ↦ y'`.  So the instance follows from the instances `(s; C → C')` and
  `(v; C' → B)` (`C' := (X', Y')`, `B := (x', y')`), both of smaller source.

The word facts of Option A were machine-checked before being proved (scratch
`bh-met-77j/sqcheck.py`: `d = 2`, words of length `≤ 6`: 814080 cases; `d = 3`, length `≤ 4`:
10748376 cases; 0 failures).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Option E**: the conjugator is the canonical descent pair of the long pair `(x, y)`. -/
def higmanVCTauShort_OptionE (d : ℕ) (p q x y : List (Fin d)) : Prop :=
  ¬ (x.length ≤ 3 ∧ y.length ≤ 3) ∧ p = higmanVCTau_pP (x, y) ∧ q = higmanVCTau_pQ (x, y)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_OptionE

/-- **Option A**: the cone swap `(p q)` carries the descent pair of `(x, y)` onto a short pair
and the descended pair onto a pair of smaller size. -/
def higmanVCTauShort_OptionA (d : ℕ) (p q x y : List (Fin d)) (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : Prop :=
  ¬ (x.length ≤ 3 ∧ y.length ≤ 3) ∧
    ∃ P' Q' X' Y' : List (Fin d),
      MapsCone (coneSwap p q hpq hqp) (higmanVCTau_pP (x, y)) P' ∧
      MapsCone (coneSwap p q hpq hqp) (higmanVCTau_pQ (x, y)) Q' ∧
      P'.length ≤ 3 ∧ Q'.length ≤ 3 ∧
      MapsCone (coneSwap p q hpq hqp) (higmanVCTau_pX (x, y)) X' ∧
      MapsCone (coneSwap p q hpq hqp) (higmanVCTau_pY (x, y)) Y' ∧
      X'.length + Y'.length < x.length + y.length

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_OptionA

/-- `L (L T L⁻¹) L⁻¹ = T` for an involution `L`. -/
theorem higmanVCTauShort_invol_cancel {H : Type*} [Group H] {L T : H} (hL : L * L = 1) :
    L * (L * T * L⁻¹) * L⁻¹ = T := by
  have hi : L⁻¹ = L := inv_eq_of_mul_eq_one_right hL
  calc L * (L * T * L⁻¹) * L⁻¹ = L * L * T * (L * L) := by
        rw [hi]
        simp only [mul_assoc]
    _ = T := by rw [hL, one_mul, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_invol_cancel

/-- **Option E.**  Conjugating by the canonical descent pair is the descent identity. -/
theorem higmanVCTauShort_optionE {d : ℕ} (hd : 1 < d) {p q x y x' y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hE : higmanVCTauShort_OptionE d p q x y)
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  unfold higmanVCTauShort_OptionE at hE
  obtain ⟨hlong, rfl, rfl⟩ := hE
  obtain ⟨hPQ, hQP, hPl, hQl, hXx, hYy, -, -⟩ := higmanVCTauConj_pair_descent hd hlong hxy hyx
  have hss := coneSwap_mul_self hPQ hQP
  have ex : x' = higmanVCTau_pX (x, y) :=
    MapsCone.unique hmx (higmanVCTauConj_mapsCone_symm hXx hss)
  have ey : y' = higmanVCTau_pY (x, y) :=
    MapsCone.unique hmy (higmanVCTauConj_mapsCone_symm hYy hss)
  subst ex ey
  unfold higmanVCTauShort_conjEq
  rw [higmanVCTauConj_psi_letter d (higmanVCTau_pP (x, y), higmanVCTau_pQ (x, y)) ⟨hPl, hQl⟩,
    higmanVCTauConj_psi_of d (x, y),
    higmanVCTauConj_psi_of d (higmanVCTau_pX (x, y), higmanVCTau_pY (x, y)),
    higmanVCTauConj_tau_descent hd hlong hxy hyx]
  exact higmanVCTauShort_invol_cancel (higmanVCTau_letter_sq d _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_optionE

/-- **Option A (the square).**  The instance `(s; A → B)` follows from `(s; C → C')` and
`(v; C' → B)` with `v := (P', Q')`. -/
theorem higmanVCTauShort_square {d : ℕ} (hd : 1 < d) {p q x y x' y' P' Q' X' Y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hlong : ¬ (x.length ≤ 3 ∧ y.length ≤ 3))
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x')
    (hP : MapsCone (coneSwap p q hpq hqp) (higmanVCTau_pP (x, y)) P')
    (hQ : MapsCone (coneSwap p q hpq hqp) (higmanVCTau_pQ (x, y)) Q')
    (hP3 : P'.length ≤ 3) (hQ3 : Q'.length ≤ 3)
    (hX : MapsCone (coneSwap p q hpq hqp) (higmanVCTau_pX (x, y)) X')
    (hY : MapsCone (coneSwap p q hpq hqp) (higmanVCTau_pY (x, y)) Y')
    (h1 : higmanVCTauShort_Inst d p q (higmanVCTau_pX (x, y)) (higmanVCTau_pY (x, y)) X' Y')
    (h2 : higmanVCTauShort_Inst d P' Q' X' Y' x' y') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨hPQ, hQP, hPl, hQl, hXx, hYy, -, -⟩ := higmanVCTauConj_pair_descent hd hlong hxy hyx
  have hss := coneSwap_mul_self hpq hqp
  have hPQ' : ¬ P' <+: Q' := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hP hss) (higmanVCTauConj_mapsCone_symm hQ hss) hPQ
  have hQP' : ¬ Q' <+: P' := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hQ hss) (higmanVCTauConj_mapsCone_symm hP hss) hQP
  have hXY : ¬ higmanVCTau_pX (x, y) <+: higmanVCTau_pY (x, y) :=
    higmanVCTauConj_not_prefix_of_maps hXx hYy hxy
  have hYX : ¬ higmanVCTau_pY (x, y) <+: higmanVCTau_pX (x, y) :=
    higmanVCTauConj_not_prefix_of_maps hYy hXx hyx
  have hXY' : ¬ X' <+: Y' := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hX hss) (higmanVCTauConj_mapsCone_symm hY hss) hXY
  have hYX' : ¬ Y' <+: X' := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hY hss) (higmanVCTauConj_mapsCone_symm hX hss) hYX
  have hv : higmanVCTauShort_conjEq d p q (higmanVCTau_pP (x, y)) (higmanVCTau_pQ (x, y))
      P' Q' :=
    higmanVCTauShort_allShort hd hpq hqp hp hq ⟨hPl, hQl, hP3, hQ3⟩ hP hQ hPQ hQP hPQ' hQP'
  have hconj : coneSwap p q hpq hqp * coneSwap _ _ hPQ hQP * (coneSwap p q hpq hqp)⁻¹ =
      coneSwap P' Q' hPQ' hQP' :=
    vgen_conj_coneSwap hPQ' hQP' hPQ hQP hP hQ
  have hdx : MapsCone (coneSwap P' Q' hPQ' hQP') X' x' := by
    rw [← hconj, mul_assoc]
    exact (hX.inv.comp hXx).comp hmx
  have hdy : MapsCone (coneSwap P' Q' hPQ' hQP') Y' y' := by
    rw [← hconj, mul_assoc]
    exact (hY.inv.comp hYy).comp hmy
  have e1 := h1 hpq hqp hp hq hX hY hXY hYX hXY' hYX'
  have e2 := h2 hPQ' hQP' hP3 hQ3 hdx hdy hXY' hYX' hxy' hyx'
  unfold higmanVCTauShort_conjEq at hv e1 e2 ⊢
  rw [higmanVCTauConj_psi_of d (x, y), higmanVCTauConj_tau_descent hd hlong hxy hyx,
    ← higmanVCTauConj_psi_of d (higmanVCTau_pX (x, y), higmanVCTau_pY (x, y)),
    ← higmanVCTauConj_psi_letter d (higmanVCTau_pP (x, y), higmanVCTau_pQ (x, y)) ⟨hPl, hQl⟩]
  exact higmanVCTauShort_conj_prod hv e1 e2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_square

end GroupApproximation.BooneHigman.Metabelian.Envelope
