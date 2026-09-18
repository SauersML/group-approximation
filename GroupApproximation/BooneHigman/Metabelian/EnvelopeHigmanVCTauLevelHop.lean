import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauLevelEasy
import GroupApproximation.Meta.AxiomGuard

/-!
# Two hops at an equal-level instance (lane bh-met-77r)

Let `(s; A → B)` be an equal-level instance, `s = (p, q)`, `A = (x, y)`, `B = (x', y')`,
`|A| = |B| = n`, with the level-`n` hypotheses `Below d n` and `Shrink d n`.

* **Hop A** (`higmanVCTauLevel_HopA`, `higmanVCTauLevel_hopA_case`).  Flexible square A of
  lane bh-met-77m with a weaker last leg: some short `w = (P, Q)` descends `A` to `C = (X, Y)`
  (`|C| < n`), `s` carries `w` to a short pair `w' = (P', Q')` and `C` to `E = (X', Y')` with
  `|E| ≤ n` (not necessarily `< n`), and the instance `(w'; E → B)` is merely *easy*
  (`higmanVCTauLevel_Easy`) instead of having a side below `n`.  Square A then applies with
  `(w; C → A)` and `(s; C → E)` from `Shrink` and `(w'; E → B)` from `higmanVCTauLevel_easy`.
* **Hop C** (`higmanVCTauLevel_HopC`, `higmanVCTauLevel_hopC_case`), conjugated conjugator.
  A short pair `r = (R, S)` carries `p, q` to short words (so `s1 := r(s)` is short and
  `ℓ_{s1} = ℓ_r ℓ_s ℓ_r⁻¹` is an all-short relator) and `A, B` to `A1, B1`; then
  `(s; A → B)` follows from the easy instances `(r; A → A1)`, `(s1; A1 → B1)`, `(r; B1 → B)`
  (`higmanVCTauLevel_groupC`).  This covers the commutation instances (`s` fixing `A`) that
  no flexible square reaches.

The word facts were model-checked by the exact scratch count `SP/bh-met-77r/exact.py`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Hop A**: flexible square A whose last leg `(P', Q'; X', Y' → x', y')` is only easy. -/
def higmanVCTauLevel_HopA (d n : ℕ) (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : Prop :=
  ∃ (P Q X Y P' Q' X' Y' : List (Fin d)) (hPQ : ¬ P <+: Q) (hQP : ¬ Q <+: P),
    P.length ≤ 3 ∧ Q.length ≤ 3 ∧
    MapsCone (coneSwap P Q hPQ hQP) X x ∧ MapsCone (coneSwap P Q hPQ hQP) Y y ∧
    X.length + Y.length < x.length + y.length ∧
    MapsCone (coneSwap p q hpq hqp) P P' ∧ MapsCone (coneSwap p q hpq hqp) Q Q' ∧
    P'.length ≤ 3 ∧ Q'.length ≤ 3 ∧
    MapsCone (coneSwap p q hpq hqp) X X' ∧ MapsCone (coneSwap p q hpq hqp) Y Y' ∧
    higmanVCTauLevel_Easy d n P' Q' X' Y' x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_HopA

/-- **Hop A case** at an equal-level top instance. -/
theorem higmanVCTauLevel_hopA_case {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hA : x.length + y.length = n)
    (hH : higmanVCTauLevel_HopA d n p q x y x' y' hpq hqp)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨P, Q, X, Y, P', Q', X', Y', hPQ, hQP, hP, hQ, hXx, hYy, hC, hsP, hsQ, hP3, hQ3,
    hX, hY, hE⟩ := hH
  have hXY : ¬ X <+: Y := higmanVCTauConj_not_prefix_of_maps hXx hYy hxy
  have hYX : ¬ Y <+: X := higmanVCTauConj_not_prefix_of_maps hYy hXx hyx
  have e0 : higmanVCTauShort_conjEq d P Q X Y x y :=
    hS P Q X Y x y (by omega) (by omega) hPQ hQP hP hQ hXx hYy hXY hYX hxy hyx
  have h1 : higmanVCTauShort_Inst d p q X Y X' Y' := hS p q X Y X' Y' (by omega) hE.1
  have h2 : higmanVCTauShort_Inst d P' Q' X' Y' x' y' :=
    fun a b c e f g i j k l => higmanVCTauLevel_easy hd hB hS a b c e f g i j k l hE
  exact higmanVCTauComm_squareA hd hpq hqp hp hq hPQ hQP hP hQ hXx hYy hmx hmy hxy hyx hxy'
    hyx' hsP hsQ hP3 hQ3 hX hY e0 h1 h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_hopA_case

/-- **Hop C**: a short pair `r = (R, S)` conjugates `s` to a short pair `s1 = (p1, q1)`, and
the three instances `(r; A → A1)`, `(s1; A1 → B1)`, `(r; B1 → B)` are easy. -/
def higmanVCTauLevel_HopC (d n : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  ∃ (R S p1 q1 x1 y1 x2 y2 : List (Fin d)) (hRS : ¬ R <+: S) (hSR : ¬ S <+: R),
    R.length ≤ 3 ∧ S.length ≤ 3 ∧
    MapsCone (coneSwap R S hRS hSR) p p1 ∧ MapsCone (coneSwap R S hRS hSR) q q1 ∧
    p1.length ≤ 3 ∧ q1.length ≤ 3 ∧
    MapsCone (coneSwap R S hRS hSR) x x1 ∧ MapsCone (coneSwap R S hRS hSR) y y1 ∧
    MapsCone (coneSwap R S hRS hSR) x' x2 ∧ MapsCone (coneSwap R S hRS hSR) y' y2 ∧
    higmanVCTauLevel_Easy d n R S x y x1 y1 ∧ higmanVCTauLevel_Easy d n p1 q1 x1 y1 x2 y2 ∧
    higmanVCTauLevel_Easy d n R S x2 y2 x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_HopC

/-- **Hop C case**, conjugated conjugator, from the level-`n` hypotheses. -/
theorem higmanVCTauLevel_hopC_case {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hH : higmanVCTauLevel_HopC d n p q x y x' y')
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨R, S, p1, q1, x1, y1, x2, y2, hRS, hSR, hR, hS3, hrp, hrq, hp1, hq1, hrx, hry,
    hrx', hry', hE1, hE2, hE3⟩ := hH
  have hrr := coneSwap_mul_self hRS hSR
  have hp1q1 : ¬ p1 <+: q1 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hrp hrr) (higmanVCTauConj_mapsCone_symm hrq hrr) hpq
  have hq1p1 : ¬ q1 <+: p1 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hrq hrr) (higmanVCTauConj_mapsCone_symm hrp hrr) hqp
  have hx1y1 : ¬ x1 <+: y1 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hrx hrr) (higmanVCTauConj_mapsCone_symm hry hrr) hxy
  have hy1x1 : ¬ y1 <+: x1 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hry hrr) (higmanVCTauConj_mapsCone_symm hrx hrr) hyx
  have hx2y2 : ¬ x2 <+: y2 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hrx' hrr) (higmanVCTauConj_mapsCone_symm hry' hrr) hxy'
  have hy2x2 : ¬ y2 <+: x2 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hry' hrr) (higmanVCTauConj_mapsCone_symm hrx' hrr) hyx'
  have hconj : coneSwap R S hRS hSR * coneSwap p q hpq hqp * (coneSwap R S hRS hSR)⁻¹ =
      coneSwap p1 q1 hp1q1 hq1p1 :=
    vgen_conj_coneSwap hp1q1 hq1p1 hpq hqp hrp hrq
  have hdx : MapsCone (coneSwap p1 q1 hp1q1 hq1p1) x1 x2 := by
    rw [← hconj, mul_assoc]
    exact (hrx.inv.comp hmx).comp hrx'
  have hdy : MapsCone (coneSwap p1 q1 hp1q1 hq1p1) y1 y2 := by
    rw [← hconj, mul_assoc]
    exact (hry.inv.comp hmy).comp hry'
  have hv : higmanVCTauShort_conjEq d R S p q p1 q1 :=
    higmanVCTauShort_allShort hd hRS hSR hR hS3 ⟨hp, hq, hp1, hq1⟩ hrp hrq hpq hqp hp1q1 hq1p1
  have e1 : higmanVCTauShort_conjEq d R S x y x1 y1 :=
    higmanVCTauLevel_easy hd hB hS hRS hSR hR hS3 hrx hry hxy hyx hx1y1 hy1x1 hE1
  have e2 : higmanVCTauShort_conjEq d p1 q1 x1 y1 x2 y2 :=
    higmanVCTauLevel_easy hd hB hS hp1q1 hq1p1 hp1 hq1 hdx hdy hx1y1 hy1x1 hx2y2 hy2x2 hE2
  have e3 : higmanVCTauShort_conjEq d R S x2 y2 x' y' :=
    higmanVCTauLevel_easy hd hB hS hRS hSR hR hS3 (higmanVCTauConj_mapsCone_symm hrx' hrr)
      (higmanVCTauConj_mapsCone_symm hry' hrr) hx2y2 hy2x2 hxy' hyx' hE3
  unfold higmanVCTauShort_conjEq at hv e1 e2 e3 ⊢
  exact higmanVCTauLevel_groupC (higmanVCTauShort_psi_sq d hR hS3) hv e1 e2 e3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauLevel_hopC_case

end GroupApproximation.BooneHigman.Metabelian.Envelope
