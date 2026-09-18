import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTauShortSquare
import GroupApproximation.Meta.AxiomGuard

/-!
# The short-conjugator family by a level induction, modulo a residual (lane bh-met-77j)

`HigmanVCTauConjShortStatement` (lane bh-met-77g) is reduced to
`HigmanVCTauShortResidualStatement`.

**Induction.**  The *level* of an instance `(s; A → B)` (`s = (p, q)` short, `A = (x, y)`,
`B = (x', y')`) is `max(|A|, |B|)`, `|A| := |x| + |y|`.  Assume every instance below level
`n` (`higmanVCTauShort_Below d n`).  Orient the instance with `|B| ≤ |A| = n`
(`higmanVCTauShort_symm`).  Then all-short instances are short relators, Option E is the
descent identity and Option A is a square (module `EnvelopeHigmanVCTauShortSquare`) whose two
smaller instances are
* `(s; C → C')`, below level `n`;
* `(v; C' → B)`, below level `n` if `|B| < n` (phase 1, `higmanVCTauShort_shrink`), and with
  source below `n` and target at level `n` if `|B| = n` (phase 2, using phase 1).
Everything else is the residual.

**Strength (loud): LOGICALLY EQUIVALENT, strictly smaller in proof content.**  The residual
is a special case of the short statement (`higmanVCTauShort_residual_of_short`), so it is
equivalent to it (`higmanVCTauShort_residual_iff`).  It is not a restatement: it only asks for
oriented instances at the top level where all-short, Option E and Option A all fail, and it
grants the level-`n` induction hypotheses (phase 1 included).  Scratch count
(`bh-met-77j/optA2.py`, oriented instances with some long word): `d = 2`, words `≤ 6`: 579k of
1552k discharged (37%); `d = 3`, words `≤ 4`: 9464k of 14203k discharged (67%).  The bulk of
the residual is equal-level instances where `(p q)` fixes `x` and `y` (commutations).

**Truth.**  The residual is implied by the short statement, which is a special case of the
conjugation family; its truth is exactly that of the family.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Remaining gap.**  Oriented top-level short-conjugator instances (`|x'| + |y'| ≤
|x| + |y| = n`) not covered by the all-short relators, Option E or Option A, under the
induction hypotheses: every instance below level `n` and, when `|x'| + |y'| = n`, every
instance with source below level `n` and target at most level `n`.  **EQUIVALENT** to
`HigmanVCTauConjShortStatement` (`higmanVCTauShort_residual_iff`), smaller in proof content. -/
def HigmanVCTauShortResidualStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ n : ℕ, higmanVCTauShort_Below d n →
    ∀ (p q x y x' y' : List (Fin d)) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p),
      p.length ≤ 3 → q.length ≤ 3 →
      x.length + y.length = n → x'.length + y'.length ≤ n →
      (x'.length + y'.length = n → higmanVCTauShort_Shrink d n) →
      ¬ (x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3) →
      ¬ higmanVCTauShort_OptionA d p q x y hpq hqp →
      ¬ higmanVCTauShort_OptionE d p q x y →
      MapsCone (coneSwap p q hpq hqp) x x' → MapsCone (coneSwap p q hpq hqp) y y' →
      ¬ x <+: y → ¬ y <+: x → ¬ x' <+: y' → ¬ y' <+: x' →
      higmanVCTauShort_conjEq d p q x y x' y'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCTauShortResidualStatement

/-- **One oriented top-level instance.** -/
theorem higmanVCTauShort_at (hR : HigmanVCTauShortResidualStatement) {d : ℕ} (hd : 1 < d)
    {n : ℕ} (hB : higmanVCTauShort_Below d n) {p q x y x' y' : List (Fin d)}
    (hA : x.length + y.length = n) (hBn : x'.length + y'.length ≤ n)
    (hSh : x'.length + y'.length = n → higmanVCTauShort_Shrink d n) :
    higmanVCTauShort_Inst d p q x y x' y' := by
  unfold higmanVCTauShort_Inst
  intro hpq hqp hp hq hmx hmy hxy hyx hxy' hyx'
  by_cases hs : x.length ≤ 3 ∧ y.length ≤ 3 ∧ x'.length ≤ 3 ∧ y'.length ≤ 3
  · exact higmanVCTauShort_allShort hd hpq hqp hp hq hs hmx hmy hxy hyx hxy' hyx'
  by_cases hE : higmanVCTauShort_OptionE d p q x y
  · exact higmanVCTauShort_optionE hd hpq hqp hE hxy hyx hmx hmy
  by_cases hOA : higmanVCTauShort_OptionA d p q x y hpq hqp
  · unfold higmanVCTauShort_OptionA at hOA
    obtain ⟨hlong, P', Q', X', Y', hP, hQ, hP3, hQ3, hX, hY, hlt⟩ := hOA
    have hC := higmanVCTauConj_len_lt hd hlong hxy hyx
    have h1 := hB p q (higmanVCTau_pX (x, y)) (higmanVCTau_pY (x, y)) X' Y'
      (by omega) (by omega)
    have h2 : higmanVCTauShort_Inst d P' Q' X' Y' x' y' := by
      by_cases hn : x'.length + y'.length = n
      · exact hSh hn P' Q' X' Y' x' y' (by omega) (by omega)
      · exact hB P' Q' X' Y' x' y' (by omega) (by omega)
    exact higmanVCTauShort_square hd hpq hqp hp hq hlong hmx hmy hxy hyx hxy' hyx' hP hQ hP3
      hQ3 hX hY h1 h2
  · exact hR d hd n hB p q x y x' y' hpq hqp hp hq hA hBn hSh hs hOA hE hmx hmy hxy hyx hxy'
      hyx'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_at

/-- **Phase 1** at level `n`: instances with source below `n` and target at most `n`. -/
theorem higmanVCTauShort_shrink (hR : HigmanVCTauShortResidualStatement) {d : ℕ} (hd : 1 < d)
    {n : ℕ} (hB : higmanVCTauShort_Below d n) : higmanVCTauShort_Shrink d n := by
  intro p q x y x' y' hA hBn
  by_cases hn : x'.length + y'.length = n
  · exact higmanVCTauShort_symm
      (higmanVCTauShort_at hR hd hB (p := p) (q := q) (x := x') (y := y') (x' := x) (y' := y)
        hn (by omega) (fun h => absurd h (by omega)))
  · exact hB p q x y x' y' hA (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_shrink

/-- **Phase 2 and the induction** on the level. -/
theorem higmanVCTauShort_below (hR : HigmanVCTauShortResidualStatement) {d : ℕ} (hd : 1 < d) :
    ∀ n : ℕ, higmanVCTauShort_Below d n := by
  intro n
  induction n with
  | zero =>
    intro p q x y x' y' h _
    exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    have hS := higmanVCTauShort_shrink hR hd ih
    intro p q x y x' y' hA hBn
    by_cases hn : x.length + y.length = n
    · exact higmanVCTauShort_at hR hd ih hn (by omega) (fun _ => hS)
    · exact hS p q x y x' y' (by omega) (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_below

/-- **Reduction.**  The residual gives the short-conjugator family. -/
theorem higmanVCTauShort_short_of_residual (hR : HigmanVCTauShortResidualStatement) :
    HigmanVCTauConjShortStatement := by
  intro d hd p q x y x' y' hpq hqp hp hq _ hmx hmy hxy hyx hxy' hyx'
  have h := higmanVCTauShort_below hR hd (x.length + y.length + x'.length + y'.length + 1)
    p q x y x' y' (by omega) (by omega) hpq hqp hp hq hmx hmy hxy hyx hxy' hyx'
  unfold higmanVCTauShort_conjEq at h
  exact (higmanVCTauConj_rel_iff d (p, q) (x, y) (x', y')).mpr h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_short_of_residual

/-- **Reduction, composed.**  The residual gives the whole conjugation family. -/
theorem higmanVCTauShort_family_of_residual (hR : HigmanVCTauShortResidualStatement) :
    HigmanVCTauConjFamilyStatement :=
  higmanVCTauConj_conjFamily_of_short (higmanVCTauShort_short_of_residual hR)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_family_of_residual

/-- The residual is a special case of the short statement. -/
theorem higmanVCTauShort_residual_of_short (h : HigmanVCTauConjShortStatement) :
    HigmanVCTauShortResidualStatement := by
  intro d hd n _ p q x y x' y' hpq hqp hp hq _ _ _ hs _ _ hmx hmy hxy hyx hxy' hyx'
  unfold higmanVCTauShort_conjEq
  exact (higmanVCTauConj_rel_iff d (p, q) (x, y) (x', y')).mp
    (h d hd p q x y x' y' hpq hqp hp hq hs hmx hmy hxy hyx hxy' hyx')

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_residual_of_short

/-- **Strength (loud): EQUIVALENT.**  The residual is logically equivalent to the short
statement (it is smaller in proof content only). -/
theorem higmanVCTauShort_residual_iff :
    HigmanVCTauShortResidualStatement ↔ HigmanVCTauConjShortStatement :=
  ⟨higmanVCTauShort_short_of_residual, higmanVCTauShort_residual_of_short⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTauShort_residual_iff

end GroupApproximation.BooneHigman.Metabelian.Envelope
