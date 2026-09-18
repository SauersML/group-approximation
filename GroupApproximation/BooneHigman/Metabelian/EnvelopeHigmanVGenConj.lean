import GroupApproximation.BooneHigman.V.ConeSwap
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugating cone swaps in `V_d`

Two facts about the cone swaps of `BooneHigman/V/ConeSwap.lean`, used to generate every cone swap
from finitely many short ones.

* `vgen_mapsCone_coneSwap_fix`: a cone swap fixes pointwise the cone of every word incomparable
  with both of its words.
* `vgen_conj_coneSwap`: if `f` carries `cone v'` onto `cone v` and `cone w'` onto `cone w` by
  prefix substitutions, then `f * coneSwap v' w' * f⁻¹ = coneSwap v w`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- A cone swap fixes the cone of a word incomparable with both of its words. -/
theorem vgen_mapsCone_coneSwap_fix {v w u : List X} (hvw : ¬ v <+: w) (hwv : ¬ w <+: v)
    (h1 : ¬ u <+: v) (h2 : ¬ v <+: u) (h3 : ¬ u <+: w) (h4 : ¬ w <+: u) :
    MapsCone (coneSwap v w hvw hwv) u u := by
  intro y
  show coneSwapFun v w (prepend u y) = prepend u y
  refine coneSwapFun_of_not (fun h => ?_) (fun h => ?_)
  · rcases prefix_or_prefix_of_isStreamPrefix h (isStreamPrefix_prepend u y) with h' | h'
    · exact h2 h'
    · exact h1 h'
  · rcases prefix_or_prefix_of_isStreamPrefix h (isStreamPrefix_prepend u y) with h' | h'
    · exact h4 h'
    · exact h3 h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_mapsCone_coneSwap_fix

/-- A stream outside `cone b` has its `f`-preimage outside `cone a` when `f` maps `a` onto `b`. -/
theorem vgen_not_prefix_inv {f : Equiv.Perm (Cantor X)} {a b : List X} (hab : MapsCone f a b)
    {x : Cantor X} (hb : ¬ IsStreamPrefix b x) : ¬ IsStreamPrefix a (f⁻¹ x) := by
  intro ha
  obtain ⟨y, hy⟩ := mem_cone_iff.mp ha
  apply hb
  have hx : x = prepend b y :=
    calc x = f (f⁻¹ x) := (f.apply_symm_apply x).symm
      _ = f (prepend a y) := by rw [hy]
      _ = prepend b y := hab y
  rw [hx]
  exact isStreamPrefix_prepend b y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_not_prefix_inv

/-- **Conjugating a cone swap** by a prefix substitution between the cones. -/
theorem vgen_conj_coneSwap {f : Equiv.Perm (Cantor X)} {v w v' w' : List X}
    (hvw : ¬ v <+: w) (hwv : ¬ w <+: v) (hvw' : ¬ v' <+: w') (hwv' : ¬ w' <+: v')
    (hv : MapsCone f v' v) (hw : MapsCone f w' w) :
    f * coneSwap v' w' hvw' hwv' * f⁻¹ = coneSwap v w hvw hwv := by
  refine Equiv.ext fun x => ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  show f (coneSwapFun v' w' (f⁻¹ x)) = coneSwapFun v w x
  by_cases hxv : IsStreamPrefix v x
  · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hxv
    rw [hv.inv y, coneSwapFun_prepend_left, coneSwapFun_prepend_left, hw y]
  · by_cases hxw : IsStreamPrefix w x
    · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hxw
      rw [hw.inv y, coneSwapFun_prepend_right hvw' hwv', coneSwapFun_prepend_right hvw hwv, hv y]
    · rw [coneSwapFun_of_not (vgen_not_prefix_inv hv hxv) (vgen_not_prefix_inv hw hxw),
        coneSwapFun_of_not hxv hxw]
      exact f.apply_symm_apply x

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_conj_coneSwap

end GroupApproximation.BooneHigman.Metabelian.Envelope
