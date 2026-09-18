import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBinMain
import GroupApproximation.Meta.AxiomGuard

/-!
# Hop family F2: generic flexible squares B and the `w`-hop (lane bh-met-92n)

Family F2 of `higmanVCTauBin_Hop`: `|p| = |q| = 3` and `x, y` incomparable with both, so
`s = ψ(p, q)` fixes `x` and `y`.  With `x = u z`, `|u| = 3`, a shorter `v` incomparable
with `u` gives the descent swap `(v, u)`:
* `higmanVCTauHop_flexBv`: if `(v, u)` fixes `p`, `q` and does not lengthen `y`, the square
  `(p, q; (x, y) → (x, y))` is flexible of kind B;
* `higmanVCTauHop_hopCw`: for a length-`≤ 3` word `w` incomparable with `p`, `q`, `x`, `y`,
  the swap `(R, S) = (p, w)` is a `HopC`, as soon as `(p, w)` and `(w, q)` are flexible B.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A cone swap read backwards (it is an involution). -/
theorem higmanVCTauHop_back {d : ℕ} {v w a b : List (Fin d)} {hvw : ¬ v <+: w}
    {hwv : ¬ w <+: v} (h : MapsCone (coneSwap v w hvw hwv) a b) :
    MapsCone (coneSwap v w hvw hwv) b a :=
  higmanVCTauConj_mapsCone_symm h (coneSwap_mul_self hvw hwv)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_back

/-- Building a flexible square B from forward images only. -/
theorem higmanVCTauHop_flexB_mk {d : ℕ} {p q x y x' y' P Q X Y p1 q1 D1 D2 : List (Fin d)}
    (hPQ : ¬ P <+: Q) (hQP : ¬ Q <+: P) (hP : P.length ≤ 3) (hQ : Q.length ≤ 3)
    (hx : MapsCone (coneSwap P Q hPQ hQP) x X) (hy : MapsCone (coneSwap P Q hPQ hQP) y Y)
    (hlt : X.length + Y.length < x.length + y.length)
    (hp : MapsCone (coneSwap P Q hPQ hQP) p p1) (hq : MapsCone (coneSwap P Q hPQ hQP) q q1)
    (hp1 : p1.length ≤ 3) (hq1 : q1.length ≤ 3)
    (hx' : MapsCone (coneSwap P Q hPQ hQP) x' D1)
    (hy' : MapsCone (coneSwap P Q hPQ hQP) y' D2)
    (hlt' : D1.length + D2.length < x.length + y.length) :
    higmanVCTauComm_FlexB d p q x y x' y' :=
  ⟨P, Q, X, Y, p1, q1, D1, D2, hPQ, hQP, hP, hQ, higmanVCTauHop_back hx,
    higmanVCTauHop_back hy, hlt, hp, hq, hp1, hq1, hx', hy', hlt'⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_flexB_mk

/-- A word of length `≤ |u|` off the cone of `x = u z` is incomparable with `u`. -/
theorem higmanVCTauHop_incU {d : ℕ} {W u x z : List (Fin d)} (hx : x = u ++ z)
    (hW : ¬ W <+: x) (hl : W.length ≤ u.length) : higmanVCTauUnif_Inc W u := by
  have hux : u <+: x := ⟨z, hx.symm⟩
  refine ⟨fun h => hW (h.trans hux), fun h => ?_⟩
  have e : u = W := h.eq_of_length (le_antisymm h.length_le hl)
  subst e
  exact hW hux

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_incU

/-- A strictly shorter word that is not a prefix is incomparable. -/
theorem higmanVCTauHop_incLen {d : ℕ} {v W : List (Fin d)} (hl : v.length < W.length)
    (h : ¬ v <+: W) : higmanVCTauUnif_Inc W v :=
  ⟨fun h' => absurd h'.length_le (by omega), h⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_incLen

/-- A word of length `≥ 2` of which the length-`2` word `v` is no prefix is incomparable
with `v`. -/
theorem higmanVCTauHop_incV {d : ℕ} {v W : List (Fin d)} (hv : v.length = 2)
    (hW : 2 ≤ W.length) (h : ¬ v <+: W) : higmanVCTauUnif_Inc W v := by
  refine ⟨fun h' => h ?_, h⟩
  have e : W = v := h'.eq_of_length (by have := h'.length_le; omega)
  subst e
  exact List.prefix_refl _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_incV

/-- The descent swap `(v, u)`, `|v| ≤ |u|`, does not lengthen a word `y` incomparable with
`v` and off the cone of `x = u z`. -/
theorem higmanVCTauHop_imgY {d : ℕ} {v u x z y : List (Fin d)} (hvu : ¬ v <+: u)
    (huv : ¬ u <+: v) (hl : v.length ≤ u.length) (hx : x = u ++ z)
    (hyv : higmanVCTauUnif_Inc y v) (hyx : ¬ y <+: x) :
    ∃ Y, MapsCone (coneSwap v u hvu huv) y Y ∧ Y.length ≤ y.length := by
  by_cases h : u <+: y
  · obtain ⟨r, rfl⟩ := h
    have e1 : (u ++ r).length = u.length + r.length := List.length_append
    have e2 : (v ++ r).length = v.length + r.length := List.length_append
    exact ⟨v ++ r, (mapsCone_coneSwap_right hvu huv).append r, by omega⟩
  · exact ⟨y, higmanVCTauUnif_fix hvu huv hyv ⟨fun h' => hyx (h'.trans ⟨z, hx.symm⟩), h⟩,
      le_refl _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_imgY

/-- **Flexible square B by a descent swap.**  If `x = u z`, `|v| < |u| ≤ 3`, `(v, u)` fixes
`p` and `q` and `y` is incomparable with `v` and off the cone of `x`, then the square
`(p, q; (x, y) → (x, y))` is flexible of kind B. -/
theorem higmanVCTauHop_flexBv {d : ℕ} {p q x y v u z : List (Fin d)} (hvu : ¬ v <+: u)
    (huv : ¬ u <+: v) (hl : v.length < u.length) (hu : u.length ≤ 3) (hx : x = u ++ z)
    (hp3 : p.length ≤ 3) (hq3 : q.length ≤ 3)
    (hpv : higmanVCTauUnif_Inc p v) (hpu : higmanVCTauUnif_Inc p u)
    (hqv : higmanVCTauUnif_Inc q v) (hqu : higmanVCTauUnif_Inc q u)
    (hyv : higmanVCTauUnif_Inc y v) (hyx : ¬ y <+: x) :
    higmanVCTauComm_FlexB d p q x y x y := by
  obtain ⟨Y, hY, hYl⟩ := higmanVCTauHop_imgY hvu huv hl.le hx hyv hyx
  subst hx
  have e1 : (u ++ z).length = u.length + z.length := List.length_append
  have e2 : (v ++ z).length = v.length + z.length := List.length_append
  have hX := (mapsCone_coneSwap_right hvu huv).append z
  exact higmanVCTauHop_flexB_mk hvu huv (by omega) hu hX hY (by omega)
    (higmanVCTauUnif_fix hvu huv hpv hpu) (higmanVCTauUnif_fix hvu huv hqv hqu) hp3 hq3
    hX hY (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_flexBv

/-- **The `w`-hop.**  If `w` is incomparable with `p`, `q`, `x`, `y` and the squares
`(p, w; (x, y) → (x, y))`, `(w, q; (x, y) → (x, y))` are flexible B, then the level-`n`
instance `(p, q; (x, y) → (x, y))` has the `HopC` witness `(R, S) = (p, w)`. -/
theorem higmanVCTauHop_hopCw {d n : ℕ} {p q w x y : List (Fin d)} (hpw : ¬ p <+: w)
    (hwp : ¬ w <+: p) (hp3 : p.length ≤ 3) (hw3 : w.length ≤ 3) (hq3 : q.length ≤ 3)
    (hqp : higmanVCTauUnif_Inc q p) (hqw : higmanVCTauUnif_Inc q w)
    (hxp : higmanVCTauUnif_Inc x p) (hxw : higmanVCTauUnif_Inc x w)
    (hyp : higmanVCTauUnif_Inc y p) (hyw : higmanVCTauUnif_Inc y w)
    (hn : x.length + y.length = n) (F1 : higmanVCTauComm_FlexB d p w x y x y)
    (F2 : higmanVCTauComm_FlexB d w q x y x y) :
    higmanVCTauLevel_HopC d n p q x y x y :=
  ⟨p, w, w, q, x, y, x, y, hpw, hwp, hp3, hw3, mapsCone_coneSwap_left hpw hwp,
    higmanVCTauUnif_fix hpw hwp hqp hqw, hw3, hq3, higmanVCTauUnif_fix hpw hwp hxp hxw,
    higmanVCTauUnif_fix hpw hwp hyp hyw, higmanVCTauUnif_fix hpw hwp hxp hxw,
    higmanVCTauUnif_fix hpw hwp hyp hyw,
    ⟨hn.le, hn.le, Or.inr (Or.inr (Or.inr (Or.inl F1)))⟩,
    ⟨hn.le, hn.le, Or.inr (Or.inr (Or.inr (Or.inl F2)))⟩,
    ⟨hn.le, hn.le, Or.inr (Or.inr (Or.inr (Or.inl F1)))⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauHop_hopCw

end GroupApproximation.BooneHigman.Metabelian.Envelope
