import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauCommSquare
import GroupApproximation.Meta.AxiomGuard

/-!
# Options R, flexible A and flexible B (lane bh-met-77m)

The case conditions discharged by `EnvelopeHigmanVCTauCommSquare`, packaged as propositions,
and the corresponding case lemmas at an equal-level top instance (`|x| + |y| = n`, with the
level-`n` induction hypotheses `higmanVCTauShort_Below d n` and `higmanVCTauShort_Shrink d n`).

* `higmanVCTauComm_OptionR`: the conjugator is the reversed canonical descent pair.
* `higmanVCTauComm_FlexA`: some short pair `(P, Q)` descends `(x, y)` to a smaller pair and the
  cone swap `(p q)` carries `P, Q` to short words and the descended pair to a smaller pair.
* `higmanVCTauComm_FlexB`: some short pair `(P, Q)` descends `(x, y)` to a smaller pair and
  carries `p, q` to short words and `(x', y')` to a smaller pair.

Scratch count (`bh-met-77m/cov.py`, `d = 2`, words `≤ 5`): of the 195584 equal-level
residual instances of lane bh-met-77j, flexible A takes 120224 and flexible B 19968 more (and
26592 are caught by the canonical flexible B); of the 13552 lower-level ones, Option R takes
3248.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Option R**: the conjugator is the canonical descent pair of `(x, y)` read backwards. -/
def higmanVCTauComm_OptionR (d : ℕ) (p q x y : List (Fin d)) : Prop :=
  ¬ (x.length ≤ 3 ∧ y.length ≤ 3) ∧ p = higmanVCTau_pQ (x, y) ∧ q = higmanVCTau_pP (x, y)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_OptionR

/-- **Flexible A**: a square A through some short descent pair `(P, Q)` of `(x, y)`. -/
def higmanVCTauComm_FlexA (d : ℕ) (p q x y : List (Fin d)) (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) : Prop :=
  ∃ (P Q X Y P' Q' X' Y' : List (Fin d)) (hPQ : ¬ P <+: Q) (hQP : ¬ Q <+: P),
    P.length ≤ 3 ∧ Q.length ≤ 3 ∧
    MapsCone (coneSwap P Q hPQ hQP) X x ∧ MapsCone (coneSwap P Q hPQ hQP) Y y ∧
    X.length + Y.length < x.length + y.length ∧
    MapsCone (coneSwap p q hpq hqp) P P' ∧ MapsCone (coneSwap p q hpq hqp) Q Q' ∧
    P'.length ≤ 3 ∧ Q'.length ≤ 3 ∧
    MapsCone (coneSwap p q hpq hqp) X X' ∧ MapsCone (coneSwap p q hpq hqp) Y Y' ∧
    X'.length + Y'.length < x.length + y.length

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_FlexA

/-- **Flexible B**: a square B through some short descent pair `(P, Q)` of `(x, y)`. -/
def higmanVCTauComm_FlexB (d : ℕ) (p q x y x' y' : List (Fin d)) : Prop :=
  ∃ (P Q X Y p1 q1 D1 D2 : List (Fin d)) (hPQ : ¬ P <+: Q) (hQP : ¬ Q <+: P),
    P.length ≤ 3 ∧ Q.length ≤ 3 ∧
    MapsCone (coneSwap P Q hPQ hQP) X x ∧ MapsCone (coneSwap P Q hPQ hQP) Y y ∧
    X.length + Y.length < x.length + y.length ∧
    MapsCone (coneSwap P Q hPQ hQP) p p1 ∧ MapsCone (coneSwap P Q hPQ hQP) q q1 ∧
    p1.length ≤ 3 ∧ q1.length ≤ 3 ∧
    MapsCone (coneSwap P Q hPQ hQP) x' D1 ∧ MapsCone (coneSwap P Q hPQ hQP) y' D2 ∧
    D1.length + D2.length < x.length + y.length

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_FlexB

/-- An identity read backwards (the letter `ψ(p, q)` is an involution). -/
theorem higmanVCTauComm_flip_eq {d : ℕ} {p q x y x' y' : List (Fin d)} (hp : p.length ≤ 3)
    (hq : q.length ≤ 3) (h : higmanVCTauShort_conjEq d p q x' y' x y) :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  unfold higmanVCTauShort_conjEq at h ⊢
  exact higmanVCTauShort_flip (higmanVCTauShort_psi_sq d hp hq) h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_flip_eq

/-- **Flexible A at the top level.** -/
theorem higmanVCTauComm_flexA_case {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hA : x.length + y.length = n) (hBn : x'.length + y'.length ≤ n)
    (hF : higmanVCTauComm_FlexA d p q x y hpq hqp)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨P, Q, X, Y, P', Q', X', Y', hPQ, hQP, hP, hQ, hXx, hYy, hC, hsP, hsQ, hP3, hQ3,
    hX, hY, hC'⟩ := hF
  have hXY : ¬ X <+: Y := higmanVCTauConj_not_prefix_of_maps hXx hYy hxy
  have hYX : ¬ Y <+: X := higmanVCTauConj_not_prefix_of_maps hYy hXx hyx
  have e0 : higmanVCTauShort_conjEq d P Q X Y x y :=
    hS P Q X Y x y (by omega) (by omega) hPQ hQP hP hQ hXx hYy hXY hYX hxy hyx
  have h1 : higmanVCTauShort_Inst d p q X Y X' Y' := hB p q X Y X' Y' (by omega) (by omega)
  have h2 : higmanVCTauShort_Inst d P' Q' X' Y' x' y' :=
    hS P' Q' X' Y' x' y' (by omega) (by omega)
  exact higmanVCTauComm_squareA hd hpq hqp hp hq hPQ hQP hP hQ hXx hYy hmx hmy hxy hyx hxy'
    hyx' hsP hsQ hP3 hQ3 hX hY e0 h1 h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_flexA_case

/-- **Flexible B at the top level.** -/
theorem higmanVCTauComm_flexB_case {d : ℕ} (hd : 1 < d) {n : ℕ}
    (hB : higmanVCTauShort_Below d n) (hS : higmanVCTauShort_Shrink d n)
    {p q x y x' y' : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hA : x.length + y.length = n) (hBn : x'.length + y'.length ≤ n)
    (hF : higmanVCTauComm_FlexB d p q x y x' y')
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨P, Q, X, Y, p1, q1, D1, D2, hPQ, hQP, hP, hQ, hXx, hYy, hC, hwp, hwq, hp1, hq1,
    hD1, hD2, hD⟩ := hF
  have hXY : ¬ X <+: Y := higmanVCTauConj_not_prefix_of_maps hXx hYy hxy
  have hYX : ¬ Y <+: X := higmanVCTauConj_not_prefix_of_maps hYy hXx hyx
  have e0 : higmanVCTauShort_conjEq d P Q X Y x y :=
    hS P Q X Y x y (by omega) (by omega) hPQ hQP hP hQ hXx hYy hXY hYX hxy hyx
  have h1 : higmanVCTauShort_Inst d p1 q1 X Y D1 D2 := hB p1 q1 X Y D1 D2 (by omega) (by omega)
  have h2 : higmanVCTauShort_Inst d P Q D1 D2 x' y' :=
    hS P Q D1 D2 x' y' (by omega) (by omega)
  exact higmanVCTauComm_squareB hd hpq hqp hp hq hPQ hQP hP hQ hXx hYy hmx hmy hxy hyx hxy'
    hyx' hwp hwq hp1 hq1 hD1 hD2 e0 h1 h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_flexB_case

end GroupApproximation.BooneHigman.Metabelian.Envelope
