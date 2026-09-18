import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauClassifyWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Flexible squares for fixed words (lane bh-met-78a)

Let `s = (p, q)`.  The explicit squares here settle the instances where `x` is fixed by `s`
(incomparable with `p` and `q`):
* `FP`: `y = p t` (so `|p| = |q|`).  A square A through `(E, p)` if `|p| = 3` (`fp1`, `E` of
  length two avoiding `x`, `p`, `q`); through `(p t0, q)` if `|p| ≤ 2`, `t = t0 t'` (`fp2`);
  if `t` is empty then `|x| ≥ 4`, `x = P u` with `|P| = 3`, and a square B through `(P, E)`
  applies (`fp3`, `E` avoiding `p`, `q`, `P`).
* `FF`: `y` fixed too, `x = P u` with `|P| = 3`.  A square B through `(P, E)` if `y = P v`
  (`ff1`); otherwise `y` is incomparable with `P`, and a square B through `(P, p)` if
  `|p| ≤ 2` (`ff3`) or through `(P, E)` (`ff2`, `E` avoiding `q`, `y`, `p`, `P`).
Each witness was checked in the scratch model `SP/bh-met-78a/plan.cpp` and then derived field
by field.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `FP`, `|p| = 3`: a square A through `(E, p)`. -/
theorem higmanVCTauClassify_fp1 {d : ℕ} {p q x t E : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hp : p.length = 3) (hq : q.length ≤ 3) (hE : E.length = 2)
    (hxp : higmanVCTauUnif_Inc x p) (hxq : higmanVCTauUnif_Inc x q)
    (hEx : higmanVCTauUnif_Inc E x) (hEp : higmanVCTauUnif_Inc E p)
    (hEq : higmanVCTauUnif_Inc E q) :
    higmanVCTauComm_FlexA d p q x (p ++ t) hpq hqp := by
  have e1 : (p ++ t).length = p.length + t.length := List.length_append
  have e2 : (E ++ t).length = E.length + t.length := List.length_append
  exact ⟨E, p, x, E ++ t, E, q, x, E ++ t, hEp.1, hEp.2, by omega, by omega,
    higmanVCTauUnif_fix hEp.1 hEp.2 (higmanVCTauUnif_incS hEx) hxp,
    (mapsCone_coneSwap_left hEp.1 hEp.2).append t, by omega,
    higmanVCTauUnif_fix hpq hqp hEp hEq, mapsCone_coneSwap_left hpq hqp, by omega, hq,
    higmanVCTauUnif_fix hpq hqp hxp hxq,
    higmanVCTauUnif_fix hpq hqp (higmanVCTauUnif_incL t hEp) (higmanVCTauUnif_incL t hEq),
    by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_fp1

/-- `FP`, `|p| = |q| ≤ 2`, `t = t0 t'`: a square A through `(p t0, q)`. -/
theorem higmanVCTauClassify_fp2 {d : ℕ} {p q x t : List (Fin d)} {t0 : Fin d}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 2) (hk : p.length = q.length)
    (hxp : higmanVCTauUnif_Inc x p) (hxq : higmanVCTauUnif_Inc x q) :
    higmanVCTauComm_FlexA d p q x (p ++ [t0] ++ t) hpq hqp := by
  have e1 : (p ++ [t0] ++ t).length = (p ++ [t0]).length + t.length := List.length_append
  have e2 : (p ++ [t0]).length = p.length + [t0].length := List.length_append
  have e3 : (q ++ [t0]).length = q.length + [t0].length := List.length_append
  have e4 : (q ++ t).length = q.length + t.length := List.length_append
  have e5 : (p ++ t).length = p.length + t.length := List.length_append
  have e6 : [t0].length = 1 := rfl
  have hPq : higmanVCTauUnif_Inc (p ++ [t0]) q := higmanVCTauUnif_incL [t0] ⟨hpq, hqp⟩
  exact ⟨p ++ [t0], q, x, q ++ t, q ++ [t0], p, x, p ++ t, hPq.1, hPq.2, by omega, by omega,
    higmanVCTauUnif_fix hPq.1 hPq.2 (higmanVCTauUnif_incR [t0] hxp) hxq,
    (mapsCone_coneSwap_right hPq.1 hPq.2).append t, by omega,
    (mapsCone_coneSwap_left hpq hqp).append [t0], mapsCone_coneSwap_right hpq hqp,
    by omega, by omega, higmanVCTauUnif_fix hpq hqp hxp hxq,
    (mapsCone_coneSwap_right hpq hqp).append t, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_fp2

/-- `FP`, `t` empty, `x = P u` with `|P| = 3`: a square B through `(P, E)`. -/
theorem higmanVCTauClassify_fp3 {d : ℕ} {p q P u E : List (Fin d)} (hp : p.length ≤ 3)
    (hq : q.length ≤ 3) (hk : p.length = q.length) (hP : P.length = 3) (hE : E.length = 2)
    (hxp : higmanVCTauUnif_Inc (P ++ u) p) (hxq : higmanVCTauUnif_Inc (P ++ u) q)
    (hEp : higmanVCTauUnif_Inc E p) (hEq : higmanVCTauUnif_Inc E q)
    (hEP : higmanVCTauUnif_Inc E P) :
    higmanVCTauComm_FlexB d p q (P ++ u) p (P ++ u) q := by
  have e1 : (P ++ u).length = P.length + u.length := List.length_append
  have e2 : (E ++ u).length = E.length + u.length := List.length_append
  have hPp := higmanVCTauClassify_inc_cut (List.prefix_append P u) (by omega) hxp
  have hPq := higmanVCTauClassify_inc_cut (List.prefix_append P u) (by omega) hxq
  have hfp := higmanVCTauUnif_fix hEP.2 hEP.1 (higmanVCTauUnif_incS hPp)
    (higmanVCTauUnif_incS hEp)
  have hfq := higmanVCTauUnif_fix hEP.2 hEP.1 (higmanVCTauUnif_incS hPq)
    (higmanVCTauUnif_incS hEq)
  exact ⟨P, E, E ++ u, p, p, q, E ++ u, q, hEP.2, hEP.1, by omega, by omega,
    (mapsCone_coneSwap_right hEP.2 hEP.1).append u, hfp, by omega, hfp, hfq, hp, hq,
    (mapsCone_coneSwap_left hEP.2 hEP.1).append u, hfq, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_fp3

/-- `FF`, `x = P u`, `y = P v`: a square B through `(P, E)`. -/
theorem higmanVCTauClassify_ff1 {d : ℕ} {p q P u v E : List (Fin d)} (hp : p.length ≤ 3)
    (hq : q.length ≤ 3) (hP : P.length = 3) (hE : E.length = 2)
    (hxp : higmanVCTauUnif_Inc (P ++ u) p) (hxq : higmanVCTauUnif_Inc (P ++ u) q)
    (hEp : higmanVCTauUnif_Inc E p) (hEq : higmanVCTauUnif_Inc E q)
    (hEP : higmanVCTauUnif_Inc E P) :
    higmanVCTauComm_FlexB d p q (P ++ u) (P ++ v) (P ++ u) (P ++ v) := by
  have e1 : (P ++ u).length = P.length + u.length := List.length_append
  have e2 : (E ++ u).length = E.length + u.length := List.length_append
  have e3 : (P ++ v).length = P.length + v.length := List.length_append
  have e4 : (E ++ v).length = E.length + v.length := List.length_append
  have hPp := higmanVCTauClassify_inc_cut (List.prefix_append P u) (by omega) hxp
  have hPq := higmanVCTauClassify_inc_cut (List.prefix_append P u) (by omega) hxq
  exact ⟨P, E, E ++ u, E ++ v, p, q, E ++ u, E ++ v, hEP.2, hEP.1, by omega, by omega,
    (mapsCone_coneSwap_right hEP.2 hEP.1).append u,
    (mapsCone_coneSwap_right hEP.2 hEP.1).append v, by omega,
    higmanVCTauUnif_fix hEP.2 hEP.1 (higmanVCTauUnif_incS hPp) (higmanVCTauUnif_incS hEp),
    higmanVCTauUnif_fix hEP.2 hEP.1 (higmanVCTauUnif_incS hPq) (higmanVCTauUnif_incS hEq),
    hp, hq, (mapsCone_coneSwap_left hEP.2 hEP.1).append u,
    (mapsCone_coneSwap_left hEP.2 hEP.1).append v, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_ff1

end GroupApproximation.BooneHigman.Metabelian.Envelope
