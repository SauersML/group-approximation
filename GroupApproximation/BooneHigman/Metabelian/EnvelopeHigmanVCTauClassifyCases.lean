import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauClassifyCone
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauClassifyFixed
import GroupApproximation.Meta.AxiomGuard

/-!
# The four position cases over `d ≥ 3` letters (lane bh-met-78a)

For a cone swap `s = (p, q)` with `|p|, |q| ≤ 3` over at least three letters, each of the
position cases `PQ` (`x = p r`, `y = q t`), `PP` (`x = p r`, `y = p t`), `FP` (`x` fixed,
`y = p t`) and `FF` (both fixed) has a flexible square (`higmanVCTauClassify_Good`), given
the side conditions of an equal-level instance that is not all short.  The explicit squares
are in `EnvelopeHigmanVCTauClassifyCone` and `EnvelopeHigmanVCTauClassifyFixed`; here the
fresh letters and words are chosen and the cases are split.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A word of length at least three splits off a prefix of length three. -/
theorem higmanVCTauClassify_split {X : Type*} {x : List X} (h : 3 ≤ x.length) :
    ∃ P u : List X, x = P ++ u ∧ P.length = 3 := by
  have e : (x.take 3).length = min 3 x.length := List.length_take
  exact ⟨x.take 3, x.drop 3, (List.take_append_drop 3 x).symm, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_split

/-- **Case `PQ`.** -/
theorem higmanVCTauClassify_casePQ {d : ℕ} (hd : 3 ≤ d) {p q r t : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hrt : 0 < r.length + t.length) :
    higmanVCTauClassify_Good d p q (p ++ r) (q ++ t) (q ++ r) (p ++ t) hpq hqp := by
  obtain ⟨c, hcp, hcq⟩ := higmanVCTauClassify_letter hd (higmanVCTauClassify_ne_nil hpq)
    (higmanVCTauClassify_ne_nil hqp)
  by_cases hq2 : 2 ≤ q.length
  · exact Or.inr (Or.inl (higmanVCTauClassify_pq1 hpq hqp hp hq hq2 hcp hcq))
  by_cases hp2 : 2 ≤ p.length
  · exact Or.inr (Or.inl (higmanVCTauClassify_pq2 hpq hqp hp hq hp2 hcp hcq))
  rcases r with _ | ⟨r0, r'⟩
  · rcases t with _ | ⟨t0, t'⟩
    · have e : ([] : List (Fin d)).length = 0 := rfl
      omega
    · rw [higmanVCTauClassify_cons_eq q t0 t']
      exact Or.inl (higmanVCTauClassify_pq4 hpq hqp (by omega) (by omega) hcp hcq)
  · rw [higmanVCTauClassify_cons_eq p r0 r']
    exact Or.inl (higmanVCTauClassify_pq3 hpq hqp (by omega) (by omega) hcp hcq)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_casePQ

/-- **Case `PP`.** -/
theorem higmanVCTauClassify_casePP {d : ℕ} (hd : 3 ≤ d) {p q r t : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hk : p.length = q.length) (hrt : ¬ r <+: t) (htr : ¬ t <+: r) :
    higmanVCTauClassify_Good d p q (p ++ r) (p ++ t) (q ++ r) (q ++ t) hpq hqp := by
  obtain ⟨c, hcp, hcq⟩ := higmanVCTauClassify_letter hd (higmanVCTauClassify_ne_nil hpq)
    (higmanVCTauClassify_ne_nil hqp)
  by_cases hp2 : 2 ≤ p.length
  · exact Or.inl (higmanVCTauClassify_pp1 hpq hqp hp hq hp2 hcp hcq)
  rcases r with _ | ⟨r0, r'⟩
  · exact absurd List.nil_prefix hrt
  rcases t with _ | ⟨t0, t'⟩
  · exact absurd List.nil_prefix htr
  rw [higmanVCTauClassify_cons_eq p r0 r', higmanVCTauClassify_cons_eq p t0 t']
  exact Or.inl (higmanVCTauClassify_pp2 hpq hqp (by omega) hk hcp hcq)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_casePP

/-- **Case `FP`.** -/
theorem higmanVCTauClassify_caseFP {d : ℕ} (hd : 3 ≤ d) {p q x t : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hk : p.length = q.length) (hxp : higmanVCTauUnif_Inc x p)
    (hxq : higmanVCTauUnif_Inc x q) (hs : 4 ≤ x.length ∨ 0 < t.length) :
    higmanVCTauClassify_Good d p q x (p ++ t) x (q ++ t) hpq hqp := by
  by_cases hp3 : p.length = 3
  · obtain ⟨E, hE, hEx, -, hEp, hEq⟩ := higmanVCTauClassify_avoid hd
      (higmanVCTauClassify_ne_nil hxp.1) (higmanVCTauClassify_ne_nil hxp.1)
      (by omega : 2 ≤ p.length) (by omega : 2 ≤ q.length)
    exact Or.inl (higmanVCTauClassify_fp1 hpq hqp hp3 hq hE hxp hxq hEx hEp hEq)
  rcases t with _ | ⟨t0, t'⟩
  · have e : ([] : List (Fin d)).length = 0 := rfl
    simp only [List.append_nil]
    obtain ⟨P, u, rfl, hP⟩ := higmanVCTauClassify_split (by omega : 3 ≤ x.length)
    obtain ⟨E, hE, hEp, hEq, hEP, -⟩ := higmanVCTauClassify_avoid hd
      (higmanVCTauClassify_ne_nil hpq) (higmanVCTauClassify_ne_nil hqp)
      (by omega : 2 ≤ P.length) (by omega : 2 ≤ P.length)
    exact Or.inr (Or.inl (higmanVCTauClassify_fp3 hp hq hk hP hE hxp hxq hEp hEq hEP))
  · rw [higmanVCTauClassify_cons_eq p t0 t']
    exact Or.inl (higmanVCTauClassify_fp2 hpq hqp (by omega) hk hxp hxq)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_caseFP

/-- **Case `FF`.** -/
theorem higmanVCTauClassify_caseFF {d : ℕ} (hd : 3 ≤ d) {p q x y : List (Fin d)}
    (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hp : p.length ≤ 3) (hq : q.length ≤ 3)
    (hxp : higmanVCTauUnif_Inc x p) (hxq : higmanVCTauUnif_Inc x q)
    (hyp : higmanVCTauUnif_Inc y p) (hyx : ¬ y <+: x) (hx : 4 ≤ x.length) :
    higmanVCTauClassify_Good d p q x y x y hpq hqp := by
  obtain ⟨P, u, rfl, hP⟩ := higmanVCTauClassify_split (by omega : 3 ≤ x.length)
  by_cases hPy : P <+: y
  · obtain ⟨v, rfl⟩ := hPy
    obtain ⟨E, hE, hEp, hEq, hEP, -⟩ := higmanVCTauClassify_avoid hd
      (higmanVCTauClassify_ne_nil hpq) (higmanVCTauClassify_ne_nil hqp)
      (by omega : 2 ≤ P.length) (by omega : 2 ≤ P.length)
    exact Or.inr (Or.inl (higmanVCTauClassify_ff1 hp hq hP hE hxp hxq hEp hEq hEP))
  have hyP : higmanVCTauUnif_Inc y P := ⟨fun h => hyx (h.trans (List.prefix_append P u)), hPy⟩
  by_cases hp2 : p.length ≤ 2
  · exact Or.inr (Or.inl (higmanVCTauClassify_ff3 hpq hqp hp2 hq hP hxp hxq hyP hyp))
  obtain ⟨E, hE, hEq, hEy, hEp, hEP⟩ := higmanVCTauClassify_avoid hd
    (higmanVCTauClassify_ne_nil hqp) (higmanVCTauClassify_ne_nil hyp.1)
    (by omega : 2 ≤ p.length) (by omega : 2 ≤ P.length)
  exact Or.inr (Or.inl (higmanVCTauClassify_ff2 hp hq hP hE hxp hxq hyP hEy hEp hEq hEP))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauClassify_caseFF

end GroupApproximation.BooneHigman.Metabelian.Envelope
