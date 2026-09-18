import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCAllReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# A canonical choice of `τ` by cone-swap descent (lane bh-met-77e)

For an incomparable pair `(v, w)` whose longer word `m` has length `≥ 3` (the other word is
`o`), put `Q := take 3 m` and `P := [a']` if `o` starts with the first letter `a` of `m`, and
`P := [a, b']` otherwise (`m = a :: b :: _`, `c'` a letter different from `c`).  Then `P`, `Q`
are incomparable, `|P| ≤ 2`, `|Q| = 3`, and the cone swap `(P Q)` carries the shorter pair
`m' := P ++ drop 3 m`, `o' := (if Q <+: o then P ++ drop 3 o else o)` onto `(m, o)`; moreover
`m'`, `o'` are incomparable, `|m'| < |m|` and `|o'| ≤ |o|`.  (These word facts are only used
for the truth of the remaining gap, and were checked by machine: see the reduce module.)

The canonical value (`higmanVCTau_val`, with fuel) of a pair is its short letter when both
words have length `≤ 3`, the conjugate `ℓ(P, Q) · val(m', o') · ℓ(P, Q)⁻¹` for a long
incomparable pair, and `1` for a long comparable pair.  This module proves that the resulting
`ψ_τ` (`τ := higmanVCTau_tau d`) kills the comparable-letter relators and the involution
relators of `higmanVC_rels d (fun _ => True)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A letter of `Fin d` (the successor mod `d`); it differs from `a` once `1 < d`. -/
def higmanVCTau_other {d : ℕ} (a : Fin d) : Fin d :=
  ⟨(a.val + 1) % d, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_other

/-- The short word `P` of the descent of the main word `m` against the other word `o`. -/
def higmanVCTau_descP {d : ℕ} : List (Fin d) → List (Fin d) → List (Fin d)
  | [], _ => []
  | [_], _ => []
  | a :: b :: _, o =>
    if o.head? = some a then [higmanVCTau_other a] else [a, higmanVCTau_other b]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_descP

/-- The descended main word `P ++ drop 3 m`. -/
def higmanVCTau_dM {d : ℕ} (m o : List (Fin d)) : List (Fin d) :=
  higmanVCTau_descP m o ++ m.drop 3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_dM

/-- The descended other word. -/
def higmanVCTau_dO {d : ℕ} (m o : List (Fin d)) : List (Fin d) :=
  if m.take 3 <+: o then higmanVCTau_descP m o ++ o.drop 3 else o

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_dO

/-- The first word `P` of the conjugating pair (the main word is the longer one). -/
def higmanVCTau_pP {d : ℕ} (p : List (Fin d) × List (Fin d)) : List (Fin d) :=
  if p.2.length ≤ p.1.length then higmanVCTau_descP p.1 p.2 else higmanVCTau_descP p.2 p.1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_pP

/-- The second word `Q` of the conjugating pair. -/
def higmanVCTau_pQ {d : ℕ} (p : List (Fin d) × List (Fin d)) : List (Fin d) :=
  if p.2.length ≤ p.1.length then p.1.take 3 else p.2.take 3

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_pQ

/-- The descended first word. -/
def higmanVCTau_pX {d : ℕ} (p : List (Fin d) × List (Fin d)) : List (Fin d) :=
  if p.2.length ≤ p.1.length then higmanVCTau_dM p.1 p.2 else higmanVCTau_dO p.2 p.1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_pX

/-- The descended second word. -/
def higmanVCTau_pY {d : ℕ} (p : List (Fin d) × List (Fin d)) : List (Fin d) :=
  if p.2.length ≤ p.1.length then higmanVCTau_dO p.1 p.2 else higmanVCTau_dM p.2 p.1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_pY

/-- The class of the short letter of `p` (and `1` if `p` is long). -/
noncomputable def higmanVCTau_letter (d : ℕ) (p : List (Fin d) × List (Fin d)) :
    higmanVC_Q d :=
  higmanVC_psiGen d (fun _ => 1) p

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_letter

/-- The canonical value of a pair, computed by descent with fuel `n`. -/
noncomputable def higmanVCTau_val (d : ℕ) : ℕ → List (Fin d) × List (Fin d) → higmanVC_Q d
  | 0, _ => 1
  | n + 1, p =>
    if p.1.length ≤ 3 ∧ p.2.length ≤ 3 then higmanVCTau_letter d p
    else if ¬ p.1 <+: p.2 ∧ ¬ p.2 <+: p.1 then
      higmanVCTau_letter d (higmanVCTau_pP p, higmanVCTau_pQ p) *
        higmanVCTau_val d n (higmanVCTau_pX p, higmanVCTau_pY p) *
          (higmanVCTau_letter d (higmanVCTau_pP p, higmanVCTau_pQ p))⁻¹
    else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_val

/-- The canonical `τ`: the descent value with fuel `|v| + |w| + 1`. -/
noncomputable def higmanVCTau_tau (d : ℕ) (p : List (Fin d) × List (Fin d)) : higmanVC_Q d :=
  higmanVCTau_val d (p.1.length + p.2.length + 1) p

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_tau

/-- Zero fuel gives `1`. -/
theorem higmanVCTau_val_zero (d : ℕ) (p : List (Fin d) × List (Fin d)) :
    higmanVCTau_val d 0 p = 1 :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_val_zero

/-- One step of the descent. -/
theorem higmanVCTau_val_succ (d n : ℕ) (p : List (Fin d) × List (Fin d)) :
    higmanVCTau_val d (n + 1) p =
      if p.1.length ≤ 3 ∧ p.2.length ≤ 3 then higmanVCTau_letter d p
      else if ¬ p.1 <+: p.2 ∧ ¬ p.2 <+: p.1 then
        higmanVCTau_letter d (higmanVCTau_pP p, higmanVCTau_pQ p) *
          higmanVCTau_val d n (higmanVCTau_pX p, higmanVCTau_pY p) *
            (higmanVCTau_letter d (higmanVCTau_pP p, higmanVCTau_pQ p))⁻¹
      else 1 :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTau_val_succ

end GroupApproximation.BooneHigman.Metabelian.Envelope
