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

end GroupApproximation.BooneHigman.Metabelian.Envelope
