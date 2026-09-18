import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauBinWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Explicit flexible squares for the binary classification (lane bh-met-78b)

The witnesses of `EnvelopeHigmanVCTauClassifyCone` / `...Fixed` use a letter avoiding both
swap words, which need not exist over `Fin 2`.  Here that letter is replaced by a short word
`C` (or `E`) incomparable with the relevant words and strictly shorter than a swap word:
* `pqB`, `pqC`: `PQ`, square B through `(q, C)` resp. `(p, C)`;
* `ppB`: `PP`, square A through `(p, C)`; `ppC`: `PP`, `|p| ≤ 2`, square A through
  `(P, p r0)`;
* `lead`: `|p| = |q| ≤ 2`, `x = a b c u` and `y` starting with a letter other than `a`: square
  A through `([a, b'], [a, b, c])`;
* `fpE`: `FP`, square A through `(E, p)`; `ffC`: `FF` with `y = P v`, square B through `(P, p)`.
Each witness was checked in the scratch model `SP/bh-met-78b/plan2.cpp`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `PQ`: a square B through `(q, C)`, `C` shorter than `q`. -/
theorem higmanVCTauBin_pqB {d : ℕ} {p q r t C : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hC : C.length < q.length)
    (hCp : higmanVCTauUnif_Inc C p) (hCq : higmanVCTauUnif_Inc C q) :
    higmanVCTauComm_FlexB d p q (p ++ r) (q ++ t) (q ++ r) (p ++ t) := by
  have e1 : (p ++ r).length = p.length + r.length := List.length_append
  have e2 : (q ++ t).length = q.length + t.length := List.length_append
  have e3 : (C ++ t).length = C.length + t.length := List.length_append
  have e4 : (C ++ r).length = C.length + r.length := List.length_append
  have e5 : (p ++ t).length = p.length + t.length := List.length_append
  have hpq' : higmanVCTauUnif_Inc p q := ⟨hpq, hqp⟩
  have hpC := higmanVCTauUnif_incS hCp
  exact ⟨q, C, p ++ r, C ++ t, p, C, C ++ r, p ++ t, hCq.2, hCq.1, hq, by omega,
    higmanVCTauUnif_fix hCq.2 hCq.1 (higmanVCTauUnif_incL r hpq') (higmanVCTauUnif_incL r hpC),
    (mapsCone_coneSwap_right hCq.2 hCq.1).append t, by omega,
    higmanVCTauUnif_fix hCq.2 hCq.1 hpq' hpC, mapsCone_coneSwap_left hCq.2 hCq.1, hp, by omega,
    (mapsCone_coneSwap_left hCq.2 hCq.1).append r,
    higmanVCTauUnif_fix hCq.2 hCq.1 (higmanVCTauUnif_incL t hpq') (higmanVCTauUnif_incL t hpC),
    by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_pqB

/-- `PQ`: a square B through `(p, C)`, `C` shorter than `p`. -/
theorem higmanVCTauBin_pqC {d : ℕ} {p q r t C : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hC : C.length < p.length)
    (hCp : higmanVCTauUnif_Inc C p) (hCq : higmanVCTauUnif_Inc C q) :
    higmanVCTauComm_FlexB d p q (p ++ r) (q ++ t) (q ++ r) (p ++ t) := by
  have e1 : (p ++ r).length = p.length + r.length := List.length_append
  have e2 : (q ++ t).length = q.length + t.length := List.length_append
  have e3 : (C ++ r).length = C.length + r.length := List.length_append
  have e4 : (C ++ t).length = C.length + t.length := List.length_append
  have e5 : (q ++ r).length = q.length + r.length := List.length_append
  have hqp' : higmanVCTauUnif_Inc q p := ⟨hqp, hpq⟩
  have hqC := higmanVCTauUnif_incS hCq
  exact ⟨p, C, C ++ r, q ++ t, C, q, q ++ r, C ++ t, hCp.2, hCp.1, hp, by omega,
    (mapsCone_coneSwap_right hCp.2 hCp.1).append r,
    higmanVCTauUnif_fix hCp.2 hCp.1 (higmanVCTauUnif_incL t hqp') (higmanVCTauUnif_incL t hqC),
    by omega, mapsCone_coneSwap_left hCp.2 hCp.1, higmanVCTauUnif_fix hCp.2 hCp.1 hqp' hqC,
    by omega, hq,
    higmanVCTauUnif_fix hCp.2 hCp.1 (higmanVCTauUnif_incL r hqp') (higmanVCTauUnif_incL r hqC),
    (mapsCone_coneSwap_left hCp.2 hCp.1).append t, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_pqC

/-- `PP`: a square A through `(p, C)`, `C` shorter than `p`. -/
theorem higmanVCTauBin_ppB {d : ℕ} {p q r t C : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hC : C.length < p.length)
    (hCp : higmanVCTauUnif_Inc C p) (hCq : higmanVCTauUnif_Inc C q) :
    higmanVCTauComm_FlexA d p q (p ++ r) (p ++ t) hpq hqp := by
  have e1 : (p ++ r).length = p.length + r.length := List.length_append
  have e2 : (p ++ t).length = p.length + t.length := List.length_append
  have e3 : (C ++ r).length = C.length + r.length := List.length_append
  have e4 : (C ++ t).length = C.length + t.length := List.length_append
  exact ⟨p, C, C ++ r, C ++ t, q, C, C ++ r, C ++ t, hCp.2, hCp.1, hp, by omega,
    (mapsCone_coneSwap_right hCp.2 hCp.1).append r,
    (mapsCone_coneSwap_right hCp.2 hCp.1).append t, by omega,
    mapsCone_coneSwap_left hpq hqp, higmanVCTauUnif_fix hpq hqp hCp hCq, hq, by omega,
    higmanVCTauUnif_fix hpq hqp (higmanVCTauUnif_incL r hCp) (higmanVCTauUnif_incL r hCq),
    higmanVCTauUnif_fix hpq hqp (higmanVCTauUnif_incL t hCp) (higmanVCTauUnif_incL t hCq),
    by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_ppB

/-- `PP`, `|p| = |q| ≤ 2`: a square A through `(P, p r0)`, `|P| = |p|`, `P` incomparable
with `p`. -/
theorem higmanVCTauBin_ppC {d : ℕ} {p q P r t : List (Fin d)} {r0 t0 : Fin d}
    {hpq : ¬ p <+: q} {hqp : ¬ q <+: p} (hk : p.length = q.length) (hp : p.length ≤ 2)
    (hP : P.length = p.length) (hPp : higmanVCTauUnif_Inc P p) :
    higmanVCTauComm_FlexA d p q (p ++ [r0] ++ r) (p ++ [t0] ++ t) hpq hqp := by
  have e1 : (p ++ [r0] ++ r).length = (p ++ [r0]).length + r.length := List.length_append
  have e2 : (p ++ [r0]).length = p.length + 1 := higmanVCTauUnif_len1 p r0
  have e3 : (p ++ [t0] ++ t).length = (p ++ [t0]).length + t.length := List.length_append
  have e4 : (p ++ [t0]).length = p.length + 1 := higmanVCTauUnif_len1 p t0
  have e5 : (P ++ r).length = P.length + r.length := List.length_append
  have e6 : (P ++ t).length = P.length + t.length := List.length_append
  have hPQ : higmanVCTauUnif_Inc P (p ++ [r0]) := higmanVCTauUnif_incR [r0] hPp
  have hX := (mapsCone_coneSwap_left hPQ.1 hPQ.2).append r
  by_cases htr : t0 = r0
  · have hY : MapsCone (coneSwap P (p ++ [r0]) hPQ.1 hPQ.2) (P ++ t) (p ++ [t0] ++ t) := by
      rw [htr]
      exact (mapsCone_coneSwap_left hPQ.1 hPQ.2).append t
    exact higmanVCTauBin_flexEq hk hPQ.1 hPQ.2 (by omega) (by omega) (by omega) (by omega) hX
      hY (by omega) (by omega) (by omega)
  · have hY := higmanVCTauUnif_fix hPQ.1 hPQ.2
      (higmanVCTauUnif_incL t (higmanVCTauUnif_incL [t0] (higmanVCTauUnif_incS hPp)))
      (higmanVCTauUnif_incL t (higmanVCTauUnif_inc_letter p htr))
    exact higmanVCTauBin_flexEq hk hPQ.1 hPQ.2 (by omega) (by omega) (by omega) (by omega) hX
      hY (by omega) (by omega) (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_ppC

/-- `|p| = |q| ≤ 2`, `x = a b c u`, `y = e y'` with `e ≠ a`: a square A through
`([a, b'], [a, b, c])`, `b' ≠ b`. -/
theorem higmanVCTauBin_lead {d : ℕ} {p q u y' : List (Fin d)} {a b c e b' : Fin d}
    {hpq : ¬ p <+: q} {hqp : ¬ q <+: p} (hk : p.length = q.length) (hp : p.length ≤ 2)
    (hbb : b' ≠ b) (hea : e ≠ a) (hyl : p.length ≤ (e :: y').length) :
    higmanVCTauComm_FlexA d p q (a :: b :: c :: u) (e :: y') hpq hqp := by
  have e1 : (a :: b :: c :: u).length = u.length + 1 + 1 + 1 := rfl
  have e2 : (a :: b' :: u).length = u.length + 1 + 1 := rfl
  have e3 : [a, b'].length = 2 := rfl
  have e4 : [a, b, c].length = 3 := rfl
  have hPQ : higmanVCTauUnif_Inc [a, b'] [a, b, c] :=
    higmanVCTauClassify_inc_cons2 a (higmanVCTauUnif_inc_cons hbb [] [c])
  have hX : MapsCone (coneSwap [a, b'] [a, b, c] hPQ.1 hPQ.2) (a :: b' :: u)
      (a :: b :: c :: u) := (mapsCone_coneSwap_left hPQ.1 hPQ.2).append u
  have hY := higmanVCTauUnif_fix hPQ.1 hPQ.2 (higmanVCTauUnif_inc_cons hea y' [b'])
    (higmanVCTauUnif_inc_cons hea y' [b, c])
  exact higmanVCTauBin_flexEq hk hPQ.1 hPQ.2 (by omega) (by omega) (by omega) (by omega) hX hY
    (by omega) hyl (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_lead

/-- `FP`: a square A through `(E, p)`, `E` shorter than `p`. -/
theorem higmanVCTauBin_fpE {d : ℕ} {p q x t E : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3) (hE : E.length < p.length)
    (hxp : higmanVCTauUnif_Inc x p) (hxq : higmanVCTauUnif_Inc x q)
    (hEx : higmanVCTauUnif_Inc E x) (hEp : higmanVCTauUnif_Inc E p)
    (hEq : higmanVCTauUnif_Inc E q) :
    higmanVCTauComm_FlexA d p q x (p ++ t) hpq hqp := by
  have e1 : (p ++ t).length = p.length + t.length := List.length_append
  have e2 : (E ++ t).length = E.length + t.length := List.length_append
  exact ⟨E, p, x, E ++ t, E, q, x, E ++ t, hEp.1, hEp.2, by omega, hp,
    higmanVCTauUnif_fix hEp.1 hEp.2 (higmanVCTauUnif_incS hEx) hxp,
    (mapsCone_coneSwap_left hEp.1 hEp.2).append t, by omega,
    higmanVCTauUnif_fix hpq hqp hEp hEq, mapsCone_coneSwap_left hpq hqp, by omega, hq,
    higmanVCTauUnif_fix hpq hqp hxp hxq,
    higmanVCTauUnif_fix hpq hqp (higmanVCTauUnif_incL t hEp) (higmanVCTauUnif_incL t hEq),
    by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_fpE

/-- `FF`, `x = P u`, `y = P v`, `|p| ≤ 2`: a square B through `(P, p)`. -/
theorem higmanVCTauBin_ffC {d : ℕ} {p q P u v : List (Fin d)} (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hp : p.length ≤ 2) (hq : q.length ≤ 3) (hP : P.length = 3)
    (hxp : higmanVCTauUnif_Inc (P ++ u) p) (hxq : higmanVCTauUnif_Inc (P ++ u) q) :
    higmanVCTauComm_FlexB d p q (P ++ u) (P ++ v) (P ++ u) (P ++ v) := by
  have e1 : (P ++ u).length = P.length + u.length := List.length_append
  have e2 : (p ++ u).length = p.length + u.length := List.length_append
  have e3 : (P ++ v).length = P.length + v.length := List.length_append
  have e4 : (p ++ v).length = p.length + v.length := List.length_append
  have hPp := higmanVCTauClassify_inc_cut (List.prefix_append P u) (by omega) hxp
  have hPq := higmanVCTauClassify_inc_cut (List.prefix_append P u) (by omega) hxq
  exact ⟨P, p, p ++ u, p ++ v, P, q, p ++ u, p ++ v, hPp.1, hPp.2, by omega, by omega,
    (mapsCone_coneSwap_right hPp.1 hPp.2).append u,
    (mapsCone_coneSwap_right hPp.1 hPp.2).append v, by omega,
    mapsCone_coneSwap_right hPp.1 hPp.2,
    higmanVCTauUnif_fix hPp.1 hPp.2 (higmanVCTauUnif_incS hPq) ⟨hqp, hpq⟩, by omega, hq,
    (mapsCone_coneSwap_left hPp.1 hPp.2).append u,
    (mapsCone_coneSwap_left hPp.1 hPp.2).append v, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauBin_ffC

end GroupApproximation.BooneHigman.Metabelian.Envelope
