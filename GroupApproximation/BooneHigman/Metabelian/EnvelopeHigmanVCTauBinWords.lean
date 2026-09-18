import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauClassifyMain
import GroupApproximation.Meta.AxiomGuard

/-!
# Word bookkeeping for the binary classification (lane bh-met-78b)

Over the binary alphabet `Fin 2` a letter different from two distinct letters is forced
(`higmanVCTauBin_eq`) and every letter has a partner (`higmanVCTauBin_flip`).  For a cone swap
`(p, q)` with `|p| = |q|` every word at least as long as `p` has an image of its own length
(`higmanVCTauBin_img`), so a square A through a short pair `(P, Q)` only has to be checked on
the source side (`higmanVCTauBin_flexEq`).  Two transports: square B is symmetric in `(p, q)`
(`higmanVCTauBin_flexB_pq`) and `Shape` passes from `p t` to `q t` (`higmanVCTauBin_shape_pq`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A binary letter different from `a` is determined. -/
theorem higmanVCTauBin_eq {a b c : Fin 2} (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  apply Fin.ext
  have h1 := a.isLt
  have h2 := b.isLt
  have h3 := c.isLt
  have h4 : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have h5 : a.val ≠ c.val := fun h => hac (Fin.ext h)
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_eq

/-- Every binary letter has a partner. -/
theorem higmanVCTauBin_flip (a : Fin 2) : ∃ b : Fin 2, b ≠ a := by
  refine ⟨⟨(a.val + 1) % 2, Nat.mod_lt _ (by omega)⟩, fun h => ?_⟩
  have h1 : (a.val + 1) % 2 = a.val := congrArg Fin.val h
  have h2 := a.isLt
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_flip

/-- With `|p| = |q|`, a word at least as long as `p` has an image of the same length. -/
theorem higmanVCTauBin_img {d : ℕ} {p q w : List (Fin d)} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hk : p.length = q.length) (hw : p.length ≤ w.length) :
    ∃ w' : List (Fin d), MapsCone (coneSwap p q hpq hqp) w w' ∧ w'.length = w.length := by
  by_cases h1 : p <+: w
  · obtain ⟨r, rfl⟩ := h1
    have e1 : (p ++ r).length = p.length + r.length := List.length_append
    have e2 : (q ++ r).length = q.length + r.length := List.length_append
    exact ⟨q ++ r, (mapsCone_coneSwap_left hpq hqp).append r, by omega⟩
  by_cases h2 : q <+: w
  · obtain ⟨r, rfl⟩ := h2
    have e1 : (p ++ r).length = p.length + r.length := List.length_append
    have e2 : (q ++ r).length = q.length + r.length := List.length_append
    exact ⟨p ++ r, (mapsCone_coneSwap_right hpq hqp).append r, by omega⟩
  have h3 : ¬ w <+: p := by
    intro h
    have e : w = p := h.eq_of_length (Nat.le_antisymm h.length_le hw)
    rw [e] at h1
    exact h1 (List.prefix_refl p)
  have h4 : ¬ w <+: q := by
    intro h
    have e : w = q := h.eq_of_length (Nat.le_antisymm h.length_le (by omega))
    rw [e] at h2
    exact h2 (List.prefix_refl q)
  exact ⟨w, higmanVCTauUnif_fix hpq hqp ⟨h3, h1⟩ ⟨h4, h2⟩, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_img

/-- With `|p| = |q|`, a square A through `(P, Q)` needs only the source-side conditions. -/
theorem higmanVCTauBin_flexEq {d : ℕ} {p q x y P Q X Y : List (Fin d)} {hpq : ¬ p <+: q}
    {hqp : ¬ q <+: p} (hk : p.length = q.length) (hPQ : ¬ P <+: Q) (hQP : ¬ Q <+: P)
    (hP : P.length ≤ 3) (hQ : Q.length ≤ 3) (hpP : p.length ≤ P.length)
    (hpQ : p.length ≤ Q.length) (hX : MapsCone (coneSwap P Q hPQ hQP) X x)
    (hY : MapsCone (coneSwap P Q hPQ hQP) Y y) (hpX : p.length ≤ X.length)
    (hpY : p.length ≤ Y.length) (hlt : X.length + Y.length < x.length + y.length) :
    higmanVCTauComm_FlexA d p q x y hpq hqp := by
  obtain ⟨P', hP', eP⟩ := higmanVCTauBin_img hpq hqp hk hpP
  obtain ⟨Q', hQ', eQ⟩ := higmanVCTauBin_img hpq hqp hk hpQ
  obtain ⟨X', hX', eX⟩ := higmanVCTauBin_img hpq hqp hk hpX
  obtain ⟨Y', hY', eY⟩ := higmanVCTauBin_img hpq hqp hk hpY
  exact ⟨P, Q, X, Y, P', Q', X', Y', hPQ, hQP, hP, hQ, hX, hY, hlt, hP', hQ', by omega,
    by omega, hX', hY', by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_flexEq

/-- A square B is symmetric in the swap words `p`, `q`. -/
theorem higmanVCTauBin_flexB_pq {d : ℕ} {p q x y x' y' : List (Fin d)}
    (h : higmanVCTauComm_FlexB d p q x y x' y') : higmanVCTauComm_FlexB d q p x y x' y' := by
  obtain ⟨P, Q, X, Y, p1, q1, D1, D2, hPQ, hQP, hP, hQ, hXx, hYy, hC, hp1, hq1, hp13, hq13, hD1,
    hD2, hC'⟩ := h
  exact ⟨P, Q, X, Y, q1, p1, D1, D2, hPQ, hQP, hP, hQ, hXx, hYy, hC, hq1, hp1, hq13, hp13, hD1,
    hD2, hC'⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_flexB_pq

/-- `Shape` passes from the cone of `p` to the cone of `q`. -/
theorem higmanVCTauBin_shape_pq {d : ℕ} {p q x t : List (Fin d)}
    (h : higmanVCTauUnif_Shape d p q x (p ++ t)) : higmanVCTauUnif_Shape d p q x (q ++ t) := by
  obtain ⟨a, c, c', t0, z, zo, t1, hz, hzo, hzz, haz, hazo, hx, hy, hw⟩ := h
  rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : t = t0 :: t1 := List.append_cancel_left hy
    exact ⟨a, c', c, t0, zo, z, t1, hzo, hz, higmanVCTauUnif_incS hzz, hazo, haz, hx,
      by rw [e], Or.inr ⟨rfl, rfl⟩⟩
  · have e1 : (zo ++ [c']).length = zo.length + 1 := higmanVCTauUnif_len1 zo c'
    have e2 : (z ++ [c]).length = z.length + 1 := higmanVCTauUnif_len1 z c
    have e : t = t0 :: t1 := (List.append_inj hy (by omega)).2
    exact ⟨a, c, c', t0, z, zo, t1, hz, hzo, hzz, haz, hazo, hx, by rw [e], Or.inr ⟨rfl, rfl⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_shape_pq

end GroupApproximation.BooneHigman.Metabelian.Envelope
