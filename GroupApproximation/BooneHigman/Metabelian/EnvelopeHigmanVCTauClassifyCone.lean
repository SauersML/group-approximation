import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauClassifyWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Flexible squares for words in the cones of `p`, `q` (lane bh-met-78a)

Let `s = (p, q)` and let `c` be a letter incomparable with `p` and `q` (it exists when
`d ≥ 3`, `higmanVCTauClassify_letter`).  The explicit squares here settle the instances where
both words lie in swapped cones:
* `PQ`: `x = p r`, `y = q t` (so `x' = q r`, `y' = p t`).  A square B through `(q, c)` if
  `|q| ≥ 2` (`pq1`), through `(p, c)` if `|p| ≥ 2` (`pq2`); otherwise a square A through
  `(p r0, c)` (`pq3`, `r = r0 r'`) or `(q t0, c)` (`pq4`, `t = t0 t'`).
* `PP`: `x = p r`, `y = p t` (so `|p| = |q|`).  A square A through `(p, c)` if `|p| ≥ 2`
  (`pp1`), else through `(p r0, c)` (`pp2`, `r = r0 r'`, `t = t0 t'`).
Each witness was checked in the scratch model `SP/bh-met-78a/plan.cpp` and then derived field
by field.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `PQ`, `|q| ≥ 2`: a square B through `(q, c)`. -/
theorem higmanVCTauClassify_pq1 {d : ℕ} {p q r t : List (Fin d)} {c : Fin d}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hq2 : 2 ≤ q.length) (hcp : higmanVCTauUnif_Inc [c] p) (hcq : higmanVCTauUnif_Inc [c] q) :
    higmanVCTauComm_FlexB d p q (p ++ r) (q ++ t) (q ++ r) (p ++ t) := by
  have e1 : (p ++ r).length = p.length + r.length := List.length_append
  have e2 : (q ++ t).length = q.length + t.length := List.length_append
  have e3 : ([c] ++ t).length = [c].length + t.length := List.length_append
  have e4 : ([c] ++ r).length = [c].length + r.length := List.length_append
  have e5 : (p ++ t).length = p.length + t.length := List.length_append
  have e6 : [c].length = 1 := rfl
  have hpq' : higmanVCTauUnif_Inc p q := ⟨hpq, hqp⟩
  have hpc := higmanVCTauUnif_incS hcp
  exact ⟨q, [c], p ++ r, [c] ++ t, p, [c], [c] ++ r, p ++ t, hcq.2, hcq.1, hq, by omega,
    higmanVCTauUnif_fix hcq.2 hcq.1 (higmanVCTauUnif_incL r hpq') (higmanVCTauUnif_incL r hpc),
    (mapsCone_coneSwap_right hcq.2 hcq.1).append t, by omega,
    higmanVCTauUnif_fix hcq.2 hcq.1 hpq' hpc, mapsCone_coneSwap_left hcq.2 hcq.1, hp, by omega,
    (mapsCone_coneSwap_left hcq.2 hcq.1).append r,
    higmanVCTauUnif_fix hcq.2 hcq.1 (higmanVCTauUnif_incL t hpq') (higmanVCTauUnif_incL t hpc),
    by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_pq1

/-- `PQ`, `|p| ≥ 2`: a square B through `(p, c)`. -/
theorem higmanVCTauClassify_pq2 {d : ℕ} {p q r t : List (Fin d)} {c : Fin d}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hp2 : 2 ≤ p.length) (hcp : higmanVCTauUnif_Inc [c] p) (hcq : higmanVCTauUnif_Inc [c] q) :
    higmanVCTauComm_FlexB d p q (p ++ r) (q ++ t) (q ++ r) (p ++ t) := by
  have e1 : (p ++ r).length = p.length + r.length := List.length_append
  have e2 : (q ++ t).length = q.length + t.length := List.length_append
  have e3 : ([c] ++ r).length = [c].length + r.length := List.length_append
  have e4 : ([c] ++ t).length = [c].length + t.length := List.length_append
  have e5 : (q ++ r).length = q.length + r.length := List.length_append
  have e6 : [c].length = 1 := rfl
  have hqp' : higmanVCTauUnif_Inc q p := ⟨hqp, hpq⟩
  have hqc := higmanVCTauUnif_incS hcq
  exact ⟨p, [c], [c] ++ r, q ++ t, [c], q, q ++ r, [c] ++ t, hcp.2, hcp.1, hp, by omega,
    (mapsCone_coneSwap_right hcp.2 hcp.1).append r,
    higmanVCTauUnif_fix hcp.2 hcp.1 (higmanVCTauUnif_incL t hqp') (higmanVCTauUnif_incL t hqc),
    by omega, mapsCone_coneSwap_left hcp.2 hcp.1, higmanVCTauUnif_fix hcp.2 hcp.1 hqp' hqc,
    by omega, hq,
    higmanVCTauUnif_fix hcp.2 hcp.1 (higmanVCTauUnif_incL r hqp') (higmanVCTauUnif_incL r hqc),
    (mapsCone_coneSwap_left hcp.2 hcp.1).append t, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_pq2

/-- `PQ`, `|p|, |q| ≤ 1`, `r = r0 r'`: a square A through `(p r0, c)`. -/
theorem higmanVCTauClassify_pq3 {d : ℕ} {p q r t : List (Fin d)} {c r0 : Fin d}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 1) (hq : q.length ≤ 1)
    (hcp : higmanVCTauUnif_Inc [c] p) (hcq : higmanVCTauUnif_Inc [c] q) :
    higmanVCTauComm_FlexA d p q (p ++ [r0] ++ r) (q ++ t) hpq hqp := by
  have e1 : (p ++ [r0] ++ r).length = (p ++ [r0]).length + r.length := List.length_append
  have e2 : (p ++ [r0]).length = p.length + [r0].length := List.length_append
  have e3 : (q ++ [r0]).length = q.length + [r0].length := List.length_append
  have e4 : (q ++ t).length = q.length + t.length := List.length_append
  have e5 : ([c] ++ r).length = [c].length + r.length := List.length_append
  have e6 : (p ++ t).length = p.length + t.length := List.length_append
  have e7 : [c].length = 1 := rfl
  have e8 : [r0].length = 1 := rfl
  have hp1 := higmanVCTauClassify_len_pos hpq
  have hq1 := higmanVCTauClassify_len_pos hqp
  have hqp' : higmanVCTauUnif_Inc q p := ⟨hqp, hpq⟩
  have hPc : higmanVCTauUnif_Inc (p ++ [r0]) [c] :=
    higmanVCTauUnif_incL [r0] (higmanVCTauUnif_incS hcp)
  exact ⟨p ++ [r0], [c], [c] ++ r, q ++ t, q ++ [r0], [c], [c] ++ r, p ++ t, hPc.1, hPc.2,
    by omega, by omega, (mapsCone_coneSwap_right hPc.1 hPc.2).append r,
    higmanVCTauUnif_fix hPc.1 hPc.2 (higmanVCTauUnif_incB t [r0] hqp')
      (higmanVCTauUnif_incL t (higmanVCTauUnif_incS hcq)), by omega,
    (mapsCone_coneSwap_left hpq hqp).append [r0], higmanVCTauUnif_fix hpq hqp hcp hcq,
    by omega, by omega,
    higmanVCTauUnif_fix hpq hqp (higmanVCTauUnif_incL r hcp) (higmanVCTauUnif_incL r hcq),
    (mapsCone_coneSwap_right hpq hqp).append t, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_pq3

end GroupApproximation.BooneHigman.Metabelian.Envelope
