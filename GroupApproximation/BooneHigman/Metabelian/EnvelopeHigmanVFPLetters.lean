import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVFPBall
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVFPSwapRel
import GroupApproximation.Meta.AxiomGuard

/-!
# The short relator families lie in `higmanVFPRelators d` (lane bh-met-77)

`higmanVFPLetter hv hw` is the free generator of the pair `(v, w)` of words of length `≤ 3`; it
evaluates to `vgenSwapOrOne v w` (`higmanVFP_lift_letter`).  Every word of reduced length `≤ 64`
killed by the evaluation lies in `higmanVFPRelators d` (`higmanVFP_mem_relators`); this places
* the comparable letters `ℓ(v, w)` (`v`, `w` comparable), value `1`;
* the involutions `ℓ(v, w)²` (`coneSwap_mul_self`);
* the symmetries `ℓ(v, w) ℓ(w, v)⁻¹` (`higmanVFP_coneSwap_comm`);
* the conjugations `ℓ(p, q) ℓ(x, y) ℓ(p, q)⁻¹ ℓ(x', y')⁻¹` when `(p q)` carries the cones `x`, `y`
  onto `x'`, `y'` (`vgen_conj_coneSwap`), and in particular the commutators of swaps of
  pairwise incomparable words (`vgen_mapsCone_coneSwap_fix`)
in the relator set.  The split relators are in `EnvelopeHigmanVFPSplitRel.lean`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A pair of words of length `≤ 3` is a short pair. -/
theorem higmanVFP_pairMem {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 3) (hw : w.length ≤ 3) :
    (v, w) ∈ vgenShortPairs (Fin d) :=
  Set.mk_mem_prod (s := {l : List (Fin d) | l.length ≤ 3}) (t := {l : List (Fin d) | l.length ≤ 3})
    hv hw

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_pairMem

/-- The free generator of the short pair `(v, w)`. -/
noncomputable def higmanVFPLetter {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 3)
    (hw : w.length ≤ 3) : FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d)))) :=
  FreeGroup.of (vgenShortEquiv (Fin d) ⟨(v, w), higmanVFP_pairMem hv hw⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFPLetter

/-- The generator of `(v, w)` evaluates to `vgenSwapOrOne v w`. -/
theorem higmanVFP_lift_letter {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 3)
    (hw : w.length ≤ 3) :
    FreeGroup.lift (vgenShortSwaps (Fin d)) (higmanVFPLetter hv hw) = vgenSwapOrOne v w := by
  simp only [higmanVFPLetter, FreeGroup.lift_apply_of, vgenShortSwaps, Equiv.symm_apply_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_lift_letter

/-- A generator has reduced length `1`. -/
theorem higmanVFP_norm_letter {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 3)
    (hw : w.length ≤ 3) : FreeGroup.norm (higmanVFPLetter hv hw) = 1 :=
  FreeGroup.norm_of _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_norm_letter

/-- Reduced length of a product of four elements. -/
theorem higmanVFP_norm_mul4 {α : Type*} [DecidableEq α] (a b c e : FreeGroup α) :
    FreeGroup.norm (a * b * c * e) ≤
      FreeGroup.norm a + FreeGroup.norm b + FreeGroup.norm c + FreeGroup.norm e :=
  (FreeGroup.norm_mul_le _ _).trans (Nat.add_le_add_right ((FreeGroup.norm_mul_le _ _).trans
    (Nat.add_le_add_right (FreeGroup.norm_mul_le _ _) _)) _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_norm_mul4

/-- **Membership criterion.**  A killed word of reduced length `≤ 64` is a relator. -/
theorem higmanVFP_mem_relators {d : ℕ} {r : FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d))))}
    (hr : FreeGroup.lift (vgenShortSwaps (Fin d)) r = 1) (hn : FreeGroup.norm r ≤ 64) :
    r ∈ higmanVFPRelators d :=
  ⟨MonoidHom.mem_ker.mpr hr, hn.trans (by unfold higmanVFPBound; omega)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_mem_relators

variable {X : Type*} [Finite X]

/-- For comparable words the swap-or-one is `1`. -/
theorem higmanVFP_swapOrOne_of_not {v w : List X} (h : ¬ (¬ v <+: w ∧ ¬ w <+: v)) :
    vgenSwapOrOne v w = 1 :=
  dif_neg h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_swapOrOne_of_not

/-- The swap-or-one is an involution. -/
theorem higmanVFP_swapOrOne_mul_self (v w : List X) :
    vgenSwapOrOne v w * vgenSwapOrOne v w = 1 := by
  by_cases h : ¬ v <+: w ∧ ¬ w <+: v
  · rw [vgenSwapOrOne_eq h.1 h.2]
    exact Subtype.ext (coneSwap_mul_self h.1 h.2)
  · rw [higmanVFP_swapOrOne_of_not h, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_swapOrOne_mul_self

/-- The swap-or-one is symmetric. -/
theorem higmanVFP_swapOrOne_symm (v w : List X) : vgenSwapOrOne v w = vgenSwapOrOne w v := by
  by_cases h : ¬ v <+: w ∧ ¬ w <+: v
  · rw [vgenSwapOrOne_eq h.1 h.2, vgenSwapOrOne_eq h.2 h.1]
    exact Subtype.ext (higmanVFP_coneSwap_comm h.1 h.2)
  · rw [higmanVFP_swapOrOne_of_not h,
      higmanVFP_swapOrOne_of_not (v := w) (w := v) fun h' => h ⟨h'.2, h'.1⟩]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_swapOrOne_symm

/-- Conjugating a swap-or-one by a cone swap carrying `x`, `y` onto `x'`, `y'`. -/
theorem higmanVFP_swapOrOne_conj {p q x y x' y' : List X} (hpq : ¬ p <+: q) (hqp : ¬ q <+: p)
    (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x')
    (hx : MapsCone (coneSwap p q hpq hqp) x x') (hy : MapsCone (coneSwap p q hpq hqp) y y') :
    vgenSwapOrOne p q * vgenSwapOrOne x y * (vgenSwapOrOne p q)⁻¹ *
      (vgenSwapOrOne x' y')⁻¹ = 1 := by
  rw [vgenSwapOrOne_eq hpq hqp, vgenSwapOrOne_eq hxy hyx, vgenSwapOrOne_eq hxy' hyx',
    mul_inv_eq_one]
  exact Subtype.ext (vgen_conj_coneSwap hxy' hyx' hxy hyx hx hy)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_swapOrOne_conj

end GroupApproximation.BooneHigman.Metabelian.Envelope
