import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauUnifWords
import GroupApproximation.Meta.AxiomGuard

/-!
# The uniform commuting leg (lane bh-met-77y)

`higmanVCTauUnif_comm_leg`: let `A = (a, v t)` with `|v| = 3`, `v` not starting with `a`, and
let `u = (u1, u2)` be a short pair fixing `A` (all of `u1, u2` incomparable with `a`, `v` and
with an auxiliary word `Qa` of length two).  Then `(u; A → A)` is a leg
(`higmanVCTauDeep_Leg`) by Hop C through `r = (a, v)`:
* `r` carries `A` to `A1 = (v, a t)` and fixes `u`;
* `(r; A → A1)` and `(r; A1 → A)` are easy by a flexible square B through `(v, w)`, where `w`
  is any length-two word incomparable with `a` and `v`;
* `(u; A1 → A1)` is easy by a flexible square A through `(v, Qa)`, where `Qa` is incomparable
  with `v` and with `a t` (for instance `Qa = a t0'` with `t0' ≠ t0`, `t = t0 t1`).

This is the sibling leg of the uniform Hop D (`EnvelopeHigmanVCTauUnifHop`) and the third leg
of the uniform Hop CD.  It was checked in the scratch model `SP/bh-met-77y/unif.py`, and each
witness was then derived field by field.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Commuting leg.**  A short pair fixing `A = (a, v t)` is a leg on `A → A`. -/
theorem higmanVCTauUnif_comm_leg {d n : ℕ} {a : Fin d} {u1 u2 v w Qa t : List (Fin d)}
    (hv : v.length = 3) (hwl : w.length = 2) (hQ : Qa.length = 2)
    (hu1 : u1.length ≤ 3) (hu2 : u2.length ≤ 3) (hn : [a].length + (v ++ t).length = n)
    (hav : higmanVCTauUnif_Inc [a] v) (haw : higmanVCTauUnif_Inc [a] w)
    (hvw : higmanVCTauUnif_Inc v w) (hQv : higmanVCTauUnif_Inc Qa v)
    (hQt : higmanVCTauUnif_Inc Qa ([a] ++ t)) (hu : higmanVCTauUnif_Inc u1 u2)
    (h1a : higmanVCTauUnif_Inc u1 [a]) (h1v : higmanVCTauUnif_Inc u1 v)
    (h1Q : higmanVCTauUnif_Inc u1 Qa) (h2a : higmanVCTauUnif_Inc u2 [a])
    (h2v : higmanVCTauUnif_Inc u2 v) (h2Q : higmanVCTauUnif_Inc u2 Qa) :
    higmanVCTauDeep_Leg d n u1 u2 [a] (v ++ t) [a] (v ++ t) := by
  have e1 : (v ++ t).length = v.length + t.length := List.length_append
  have e2 : (w ++ t).length = w.length + t.length := List.length_append
  have e3 : ([a] ++ t).length = [a].length + t.length := List.length_append
  have e4 : [a].length = 1 := rfl
  have hat := higmanVCTauUnif_incL t hav
  have hFB : higmanVCTauComm_FlexB d [a] v [a] (v ++ t) v ([a] ++ t) :=
    ⟨v, w, [a], w ++ t, [a], w, w, [a] ++ t, hvw.1, hvw.2, by omega, by omega,
      higmanVCTauUnif_fix hvw.1 hvw.2 hav haw,
      (mapsCone_coneSwap_right hvw.1 hvw.2).append t, by omega,
      higmanVCTauUnif_fix hvw.1 hvw.2 hav haw, mapsCone_coneSwap_left hvw.1 hvw.2,
      by omega, by omega, mapsCone_coneSwap_left hvw.1 hvw.2,
      higmanVCTauUnif_fix hvw.1 hvw.2 hat (higmanVCTauUnif_incL t haw), by omega⟩
  have hvQ := higmanVCTauUnif_incS hQv
  have hFA : higmanVCTauComm_FlexA d u1 u2 v ([a] ++ t) hu.1 hu.2 :=
    ⟨v, Qa, Qa, [a] ++ t, v, Qa, Qa, [a] ++ t, hvQ.1, hvQ.2, by omega, by omega,
      mapsCone_coneSwap_right hvQ.1 hvQ.2,
      higmanVCTauUnif_fix hvQ.1 hvQ.2 hat (higmanVCTauUnif_incS hQt), by omega,
      higmanVCTauUnif_fix hu.1 hu.2 (higmanVCTauUnif_incS h1v) (higmanVCTauUnif_incS h2v),
      higmanVCTauUnif_fix hu.1 hu.2 (higmanVCTauUnif_incS h1Q) (higmanVCTauUnif_incS h2Q),
      by omega, by omega,
      higmanVCTauUnif_fix hu.1 hu.2 (higmanVCTauUnif_incS h1Q) (higmanVCTauUnif_incS h2Q),
      higmanVCTauUnif_fix hu.1 hu.2 (higmanVCTauUnif_incL t (higmanVCTauUnif_incS h1a))
        (higmanVCTauUnif_incL t (higmanVCTauUnif_incS h2a)), by omega⟩
  exact Or.inr (Or.inr (Or.inr
    ⟨[a], v, u1, u2, v, [a] ++ t, v, [a] ++ t, hav.1, hav.2, by omega, by omega,
      higmanVCTauUnif_fix hav.1 hav.2 h1a h1v, higmanVCTauUnif_fix hav.1 hav.2 h2a h2v,
      hu1, hu2, mapsCone_coneSwap_left hav.1 hav.2,
      (mapsCone_coneSwap_right hav.1 hav.2).append t, mapsCone_coneSwap_left hav.1 hav.2,
      (mapsCone_coneSwap_right hav.1 hav.2).append t,
      ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inl hFB)))⟩,
      ⟨by omega, by omega, Or.inr (Or.inr (Or.inl ⟨hu.1, hu.2, hFA⟩))⟩,
      ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hFB))))⟩⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauUnif_comm_leg

end GroupApproximation.BooneHigman.Metabelian.Envelope
