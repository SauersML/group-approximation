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

/-- **Comparable letters are relators.** -/
theorem higmanVFP_letter_comparable_mem {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 3)
    (hw : w.length ≤ 3) (h : ¬ (¬ v <+: w ∧ ¬ w <+: v)) :
    higmanVFPLetter hv hw ∈ higmanVFPRelators d :=
  higmanVFP_mem_relators ((higmanVFP_lift_letter hv hw).trans (higmanVFP_swapOrOne_of_not h))
    ((higmanVFP_norm_letter hv hw).trans_le (by norm_num))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_letter_comparable_mem

/-- **Involution relators.** -/
theorem higmanVFP_letter_sq_mem {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 3)
    (hw : w.length ≤ 3) :
    higmanVFPLetter hv hw * higmanVFPLetter hv hw ∈ higmanVFPRelators d :=
  higmanVFP_mem_relators
    (by
      simp only [map_mul, higmanVFP_lift_letter]
      exact higmanVFP_swapOrOne_mul_self v w)
    ((FreeGroup.norm_mul_le _ _).trans (by norm_num [higmanVFP_norm_letter]))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_letter_sq_mem

/-- **Symmetry relators.** -/
theorem higmanVFP_letter_symm_mem {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 3)
    (hw : w.length ≤ 3) :
    higmanVFPLetter hv hw * (higmanVFPLetter hw hv)⁻¹ ∈ higmanVFPRelators d :=
  higmanVFP_mem_relators
    (by
      simp only [map_mul, map_inv, higmanVFP_lift_letter]
      exact mul_inv_eq_one.mpr (higmanVFP_swapOrOne_symm v w))
    ((FreeGroup.norm_mul_le _ _).trans
      (by norm_num [FreeGroup.norm_inv_eq, higmanVFP_norm_letter]))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_letter_symm_mem

/-- **Conjugation relators.**  If `(p q)` carries the cones `x`, `y` onto `x'`, `y'`, then
`ℓ(p, q) ℓ(x, y) ℓ(p, q)⁻¹ ℓ(x', y')⁻¹` is a relator. -/
theorem higmanVFP_letter_conj_mem {d : ℕ} {p q x y x' y' : List (Fin d)} (hpl : p.length ≤ 3)
    (hql : q.length ≤ 3) (hxl : x.length ≤ 3) (hyl : y.length ≤ 3) (hxl' : x'.length ≤ 3)
    (hyl' : y'.length ≤ 3) (hpq : ¬ p <+: q) (hqp : ¬ q <+: p) (hxy : ¬ x <+: y)
    (hyx : ¬ y <+: x) (hxy' : ¬ x' <+: y') (hyx' : ¬ y' <+: x')
    (hx : MapsCone (coneSwap p q hpq hqp) x x') (hy : MapsCone (coneSwap p q hpq hqp) y y') :
    higmanVFPLetter hpl hql * higmanVFPLetter hxl hyl * (higmanVFPLetter hpl hql)⁻¹ *
      (higmanVFPLetter hxl' hyl')⁻¹ ∈ higmanVFPRelators d :=
  higmanVFP_mem_relators
    (by
      simp only [map_mul, map_inv, higmanVFP_lift_letter]
      exact higmanVFP_swapOrOne_conj hpq hqp hxy hyx hxy' hyx' hx hy)
    ((higmanVFP_norm_mul4 _ _ _ _).trans
      (by norm_num [FreeGroup.norm_inv_eq, higmanVFP_norm_letter]))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_letter_conj_mem

/-- **Commutation relators.**  Swaps of pairwise incomparable words commute. -/
theorem higmanVFP_letter_comm_mem {d : ℕ} {p q x y : List (Fin d)} (hpl : p.length ≤ 3)
    (hql : q.length ≤ 3) (hxl : x.length ≤ 3) (hyl : y.length ≤ 3) (hpq : ¬ p <+: q)
    (hqp : ¬ q <+: p) (hxy : ¬ x <+: y) (hyx : ¬ y <+: x) (hxp : ¬ x <+: p) (hpx : ¬ p <+: x)
    (hxq : ¬ x <+: q) (hqx : ¬ q <+: x) (hyp : ¬ y <+: p) (hpy : ¬ p <+: y) (hyq : ¬ y <+: q)
    (hqy : ¬ q <+: y) :
    higmanVFPLetter hpl hql * higmanVFPLetter hxl hyl * (higmanVFPLetter hpl hql)⁻¹ *
      (higmanVFPLetter hxl hyl)⁻¹ ∈ higmanVFPRelators d :=
  higmanVFP_letter_conj_mem hpl hql hxl hyl hxl hyl hpq hqp hxy hyx hxy hyx
    (vgen_mapsCone_coneSwap_fix hpq hqp hxp hpx hxq hqx)
    (vgen_mapsCone_coneSwap_fix hpq hqp hyp hpy hyq hqy)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_letter_comm_mem

end GroupApproximation.BooneHigman.Metabelian.Envelope
