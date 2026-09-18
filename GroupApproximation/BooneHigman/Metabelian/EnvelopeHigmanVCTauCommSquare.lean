import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauShortSquare
import GroupApproximation.Meta.AxiomGuard

/-!
# Flexible squares and the reversed descent pair (lane bh-met-77m)

Let `s := (p, q)` be a short conjugator and `A := (x, y)`, `B := (x', y')` with
`(p q) : x ↦ x', y ↦ y'`.  Write `ℓ_u := ψ(u)` and `τ_C := ψ(C)` for pairs `u`, `C`.

* **Flexible square A** (`higmanVCTauComm_squareA`).  Option A of lane bh-met-77j uses the
  *canonical* descent pair of `A`.  Here any short pair `w := (P, Q)` with
  `(P Q) : X ↦ x, Y ↦ y` works, provided the descent identity `ℓ_w τ_C ℓ_w⁻¹ = τ_A` for
  `C := (X, Y)` is supplied as a hypothesis `e0` (at the top level it is an instance with
  source below the level, so the induction supplies it).
* **Flexible square B** (`higmanVCTauComm_squareB`).  Instead of pushing the descent pair
  through `s`, push `s` through the descent pair: `(P Q)` carries `p ↦ p1`, `q ↦ q1` (short),
  so `s1 := (p1, q1)` has `ℓ_w ℓ_s ℓ_w⁻¹ = ℓ_{s1}` (a short relator) and
  `(p1 q1) = (P Q)(p q)(P Q)⁻¹`.  If `(P Q)` carries `x' ↦ D1`, `y' ↦ D2` then the instance
  follows from `(w; C → A)`, `(s1; C → D)` and `(w; D → B)`, `D := (D1, D2)`.
* **Reversed descent pair** (`higmanVCTauComm_erev`).  `s = (Q, P)` for the canonical
  descent pair `(P, Q)` of `A`: the cone swaps agree (`higmanVCTauComm_coneSwap_comm`) and
  `ℓ_{(P,Q)} = ℓ_{(Q,P)}` (an all-short relator), so this is Option E.

The word facts used by the flexible squares were model-checked in the permutation model
(scratch `bh-met-77m/sanity.py`, `d = 2`, words `≤ 4`: 257440 flexible-A and 234944
flexible-B instances, 0 failures).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The cone swap does not depend on the order of its two words. -/
theorem higmanVCTauComm_coneSwap_comm {X : Type*} {v w : List X} (hvw : ¬ v <+: w)
    (hwv : ¬ w <+: v) : coneSwap w v hwv hvw = coneSwap v w hvw hwv := by
  have h := vgen_conj_coneSwap hwv hvw hvw hwv (mapsCone_coneSwap_left hvw hwv)
    (mapsCone_coneSwap_right hvw hwv)
  rw [mul_inv_cancel_right] at h
  exact h.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_coneSwap_comm

/-- The group identity behind square B. -/
theorem higmanVCTauComm_groupB {G : Type*} [Group G] {Lw Ls Ls1 TC TA TD TB : G}
    (hL : Lw * Lw = 1) (hv : Lw * Ls * Lw⁻¹ = Ls1) (e0 : Lw * TC * Lw⁻¹ = TA)
    (e1 : Ls1 * TC * Ls1⁻¹ = TD) (e2 : Lw * TD * Lw⁻¹ = TB) : Ls * TA * Ls⁻¹ = TB := by
  have hi : Lw⁻¹ = Lw := inv_eq_of_mul_eq_one_right hL
  have hb : ∀ z : G, Lw * (Lw * z) = z := fun z => by rw [← mul_assoc, hL, one_mul]
  subst hv e0 e1 e2
  rw [hi, mul_inv_rev, mul_inv_rev, hi]
  simp only [mul_assoc, hb, hL, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_groupB

/-- **Flexible square A.**  The instance `(s; A → B)` follows from the descent identity
`e0 : (w; C → A)`, and the instances `(s; C → C')` and `(v; C' → B)`, `v := (P', Q')`. -/
theorem higmanVCTauComm_squareA {d : ℕ} (hd : 1 < d)
    {p q x y x' y' P Q X Y P' Q' X' Y' : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hPQ : ¬ P <+: Q) (hQP : ¬ Q <+: P) (hP : P.length ≤ 3) (hQ : Q.length ≤ 3)
    (hXx : MapsCone (coneSwap P Q hPQ hQP) X x) (hYy : MapsCone (coneSwap P Q hPQ hQP) Y y)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x')
    (hsP : MapsCone (coneSwap p q hpq hqp) P P') (hsQ : MapsCone (coneSwap p q hpq hqp) Q Q')
    (hP3 : P'.length ≤ 3) (hQ3 : Q'.length ≤ 3)
    (hX : MapsCone (coneSwap p q hpq hqp) X X') (hY : MapsCone (coneSwap p q hpq hqp) Y Y')
    (e0 : higmanVCTauShort_conjEq d P Q X Y x y)
    (h1 : higmanVCTauShort_Inst d p q X Y X' Y')
    (h2 : higmanVCTauShort_Inst d P' Q' X' Y' x' y') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hss := coneSwap_mul_self hpq hqp
  have hPQ' : ¬ P' <+: Q' := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hsP hss) (higmanVCTauConj_mapsCone_symm hsQ hss) hPQ
  have hQP' : ¬ Q' <+: P' := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hsQ hss) (higmanVCTauConj_mapsCone_symm hsP hss) hQP
  have hXY : ¬ X <+: Y := higmanVCTauConj_not_prefix_of_maps hXx hYy hxy
  have hYX : ¬ Y <+: X := higmanVCTauConj_not_prefix_of_maps hYy hXx hyx
  have hXY' : ¬ X' <+: Y' := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hX hss) (higmanVCTauConj_mapsCone_symm hY hss) hXY
  have hYX' : ¬ Y' <+: X' := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hY hss) (higmanVCTauConj_mapsCone_symm hX hss) hYX
  have hv : higmanVCTauShort_conjEq d p q P Q P' Q' :=
    higmanVCTauShort_allShort hd hpq hqp hp hq ⟨hP, hQ, hP3, hQ3⟩ hsP hsQ hPQ hQP hPQ' hQP'
  have hconj : coneSwap p q hpq hqp * coneSwap P Q hPQ hQP * (coneSwap p q hpq hqp)⁻¹ =
      coneSwap P' Q' hPQ' hQP' :=
    vgen_conj_coneSwap hPQ' hQP' hPQ hQP hsP hsQ
  have hdx : MapsCone (coneSwap P' Q' hPQ' hQP') X' x' := by
    rw [← hconj, mul_assoc]
    exact (hX.inv.comp hXx).comp hmx
  have hdy : MapsCone (coneSwap P' Q' hPQ' hQP') Y' y' := by
    rw [← hconj, mul_assoc]
    exact (hY.inv.comp hYy).comp hmy
  have e1 := h1 hpq hqp hp hq hX hY hXY hYX hXY' hYX'
  have e2 := h2 hPQ' hQP' hP3 hQ3 hdx hdy hXY' hYX' hxy' hyx'
  unfold higmanVCTauShort_conjEq at hv e0 e1 e2 ⊢
  rw [← e0]
  exact higmanVCTauShort_conj_prod hv e1 e2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_squareA

/-- **Flexible square B.**  The instance `(s; A → B)` follows from the descent identity
`e0 : (w; C → A)` and the instances `(s1; C → D)` and `(w; D → B)`, `s1 := (p1, q1)`. -/
theorem higmanVCTauComm_squareB {d : ℕ} (hd : 1 < d)
    {p q x y x' y' P Q X Y p1 q1 D1 D2 : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hPQ : ¬ P <+: Q) (hQP : ¬ Q <+: P) (hP : P.length ≤ 3) (hQ : Q.length ≤ 3)
    (hXx : MapsCone (coneSwap P Q hPQ hQP) X x) (hYy : MapsCone (coneSwap P Q hPQ hQP) Y y)
    (hmx : MapsCone (coneSwap p q hpq hqp) x x') (hmy : MapsCone (coneSwap p q hpq hqp) y y')
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x')
    (hwp : MapsCone (coneSwap P Q hPQ hQP) p p1) (hwq : MapsCone (coneSwap P Q hPQ hQP) q q1)
    (hp1 : p1.length ≤ 3) (hq1 : q1.length ≤ 3)
    (hD1 : MapsCone (coneSwap P Q hPQ hQP) x' D1) (hD2 : MapsCone (coneSwap P Q hPQ hQP) y' D2)
    (e0 : higmanVCTauShort_conjEq d P Q X Y x y)
    (h1 : higmanVCTauShort_Inst d p1 q1 X Y D1 D2)
    (h2 : higmanVCTauShort_Inst d P Q D1 D2 x' y') :
    higmanVCTauShort_conjEq d p q x y x' y' := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hww := coneSwap_mul_self hPQ hQP
  have hp1q1 : ¬ p1 <+: q1 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hwp hww) (higmanVCTauConj_mapsCone_symm hwq hww) hpq
  have hq1p1 : ¬ q1 <+: p1 := higmanVCTauConj_not_prefix_of_maps
    (higmanVCTauConj_mapsCone_symm hwq hww) (higmanVCTauConj_mapsCone_symm hwp hww) hqp
  have hXY : ¬ X <+: Y := higmanVCTauConj_not_prefix_of_maps hXx hYy hxy
  have hYX : ¬ Y <+: X := higmanVCTauConj_not_prefix_of_maps hYy hXx hyx
  have hDx := higmanVCTauConj_mapsCone_symm hD1 hww
  have hDy := higmanVCTauConj_mapsCone_symm hD2 hww
  have hD12 : ¬ D1 <+: D2 := higmanVCTauConj_not_prefix_of_maps hDx hDy hxy'
  have hD21 : ¬ D2 <+: D1 := higmanVCTauConj_not_prefix_of_maps hDy hDx hyx'
  have hv : higmanVCTauShort_conjEq d P Q p q p1 q1 :=
    higmanVCTauShort_allShort hd hPQ hQP hP hQ ⟨hp, hq, hp1, hq1⟩ hwp hwq hpq hqp hp1q1 hq1p1
  have hconj : coneSwap P Q hPQ hQP * coneSwap p q hpq hqp * (coneSwap P Q hPQ hQP)⁻¹ =
      coneSwap p1 q1 hp1q1 hq1p1 :=
    vgen_conj_coneSwap hp1q1 hq1p1 hpq hqp hwp hwq
  have hdx : MapsCone (coneSwap p1 q1 hp1q1 hq1p1) X D1 := by
    rw [← hconj, mul_assoc]
    exact ((higmanVCTauConj_mapsCone_symm hXx hww).inv.comp hmx).comp hD1
  have hdy : MapsCone (coneSwap p1 q1 hp1q1 hq1p1) Y D2 := by
    rw [← hconj, mul_assoc]
    exact ((higmanVCTauConj_mapsCone_symm hYy hww).inv.comp hmy).comp hD2
  have e1 := h1 hp1q1 hq1p1 hp1 hq1 hdx hdy hXY hYX hD12 hD21
  have e2 := h2 hPQ hQP hP hQ hDx hDy hD12 hD21 hxy' hyx'
  unfold higmanVCTauShort_conjEq at hv e0 e1 e2 ⊢
  exact higmanVCTauComm_groupB (higmanVCTauShort_psi_sq d hP hQ) hv e0 e1 e2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_squareB

/-- **Reversed descent pair.**  Conjugating by `(Q, P)`, the canonical descent pair of `(x, y)`
read backwards, is again the descent identity. -/
theorem higmanVCTauComm_erev {d : ℕ} (hd : 1 < d) {x y x' y' : List (Fin d)}
    (hlong : ¬ (x.length ≤ 3 ∧ y.length ≤ 3))
    (hpq : ¬ higmanVCTau_pQ (x, y) <+: higmanVCTau_pP (x, y))
    (hqp : ¬ higmanVCTau_pP (x, y) <+: higmanVCTau_pQ (x, y))
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (hmx : MapsCone (coneSwap _ _ hpq hqp) x x') (hmy : MapsCone (coneSwap _ _ hpq hqp) y y') :
    higmanVCTauShort_conjEq d (higmanVCTau_pQ (x, y)) (higmanVCTau_pP (x, y)) x y x' y' := by
  obtain ⟨_, _, hPl, hQl, -⟩ := higmanVCTauConj_pair_descent hd hlong hxy hyx
  rw [higmanVCTauComm_coneSwap_comm hqp hpq] at hmx hmy
  have hE0 : higmanVCTauShort_OptionE d (higmanVCTau_pP (x, y)) (higmanVCTau_pQ (x, y)) x y := by
    unfold higmanVCTauShort_OptionE
    exact ⟨hlong, rfl, rfl⟩
  have hE := higmanVCTauShort_optionE hd hqp hpq hE0 hxy hyx hmx hmy
  have hsw : higmanVCTauShort_conjEq d (higmanVCTau_pP (x, y)) (higmanVCTau_pQ (x, y))
      (higmanVCTau_pP (x, y)) (higmanVCTau_pQ (x, y)) (higmanVCTau_pQ (x, y))
      (higmanVCTau_pP (x, y)) :=
    higmanVCTauShort_allShort hd hqp hpq hPl hQl ⟨hPl, hQl, hQl, hPl⟩
      (mapsCone_coneSwap_left hqp hpq) (mapsCone_coneSwap_right hqp hpq) hqp hpq hpq hqp
  unfold higmanVCTauShort_conjEq at hsw hE ⊢
  rw [mul_inv_cancel_right] at hsw
  rw [← hsw]
  exact hE

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauComm_erev

end GroupApproximation.BooneHigman.Metabelian.Envelope
