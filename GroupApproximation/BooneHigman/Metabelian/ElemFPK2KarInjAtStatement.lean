import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarInjAtTriv
import GroupApproximation.Meta.AxiomGuard

/-!
# The proper Karoubi residual `k2KarInjAt_ProperAt`

Lane `bh-met-92o`, statement module.  Target: `k2Karoubi_InjAt s` (`R1`).
Notation: `P = A ×_L L[X]`, `L = A_s`.

* `k2KarInjAt_snd_injective_of_regular`: for regular `s`, `snd : P → L[X]` is injective at the
  ring level.  This is the formal content of the LOUD note in `ElemFPK2KarInjAtTriv`: the
  suggested route's generators `x(ker snd)` are trivial, so the route collapses to `R1`.
* `k2KarInjAt_ProperAt s`: `R1` at `s` for a non-unit, non-nilpotent `s`.
* `k2KarInjAt_injAt_of_properAt`: `ProperAt s → R1 s`.  The unit case is
  `k2KarInjAt_of_isUnit` and the nilpotent case is `k2KarInjAt_of_isNilpotent`.
* `k2KarInjAt_properAt_of_injAt`: the trivial converse.

## Truth check

`ProperAt s` is true for the Pos family `s = C s₀` (`s₀ ≠ 0` a non-unit of
`F_p[s_1..s_k]`).  There it is `R1` itself, which is `K₂`-injectivity for the Karoubi square
`P → A`, `P → P_s = L[X]`: `s` is regular on `P` and `P / s^N ≅ A / s^N`.  This is an informal
argument, not a hypothesis.

A script in `$SP/bh-met-92o/` checks finite models.  For a finite ring `A`, `A_s` is a factor
of `A`, so `R1` holds there by a retraction.  Over `A = ℤ`, `s = 2`, it checks at matrix level
that the `conj_opp` witness words `W(a, n; h)` and `W(a s, n + 1; h)` have equal images in
`GL(3, L[X])` and trivial `fst`-images.  Their quotient is therefore a genuine element of
`ker fst ∩ ker snd`: a nontrivial Steinberg word, whose death `R1` asserts.

## LOUD: the residual is only EQUIVALENT to `R1`

`k2KarInjAt_ProperAt s ↔ k2Karoubi_InjAt s` holds for every `s`; both directions are proved
below.  So the residual is **NOT strictly weaker in logical strength**.  It is strictly
smaller only in proof content: the unit, nilpotent, `L = 0` and retract cases are discharged
unconditionally.

On the Pos family the hypotheses `¬ IsUnit`, `¬ IsNilpotent` always hold, so there
`ProperAt (C s₀)` is **literally `R1`**.  The genuine gap is `K₂` Karoubi-square injectivity
for the non-surjective map `snd`.  Nothing here uses excision, homotopy invariance, dilation,
`k2PullRel_ActionAt`, or a citation.
-/

universe u

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section KarInjAtStatement

variable {A : Type u} [CommRing A] {s : A}

/-- A regular element stays regular in every power. -/
theorem k2KarInjAt_pow_regular (hreg : ∀ a : A, s * a = 0 → a = 0) :
    ∀ (k : ℕ) (a : A), s ^ k * a = 0 → a = 0
  | 0, a, h => by rwa [pow_zero, one_mul] at h
  | k + 1, a, h =>
    k2KarInjAt_pow_regular hreg k a (hreg _ (by rwa [pow_succ', mul_assoc] at h))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInjAt_pow_regular

/-- **LOUD support**: for regular `s`, the ring-level kernel of `snd : P → L[X]` is `0`. -/
theorem k2KarInjAt_snd_injective_of_regular (hreg : ∀ a : A, s * a = 0 → a = 0) :
    Function.Injective (k2PullRel_snd s) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  have h0 : algebraMap A (Localization.Away s) (k2PullRel_fst s b) = 0 := by
    rw [← k2PullRel_eval_snd, hb, Polynomial.eval_zero]
  obtain ⟨⟨m, hm⟩, hmb⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers s) (Localization.Away s) _).mp h0
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff m s).mp hm
  have hf : k2PullRel_fst s b = 0 := k2KarInjAt_pow_regular hreg k _ hmb
  exact k2PullRel_ext (by rw [hf, map_zero]) (by rw [hb, map_zero])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInjAt_snd_injective_of_regular

/-- **The proper Karoubi residual**: `R1` at a non-unit, non-nilpotent `s`.
**LOUD**: equivalent to `R1` (see the module docstring). -/
def k2KarInjAt_ProperAt (s : A) : Prop :=
  ¬ IsUnit s → ¬ IsNilpotent s → k2Karoubi_InjAt s

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInjAt_ProperAt

/-- **Reduction**: the proper residual gives `R1`; the degenerate cases are unconditional. -/
theorem k2KarInjAt_injAt_of_properAt (h : k2KarInjAt_ProperAt s) : k2Karoubi_InjAt s := by
  by_cases hu : IsUnit s
  · exact k2KarInjAt_of_isUnit hu
  by_cases hn : IsNilpotent s
  · exact k2KarInjAt_of_isNilpotent hn
  exact h hu hn

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInjAt_injAt_of_properAt

/-- **LOUD converse**: `R1` gives the proper residual, so the two are equivalent. -/
theorem k2KarInjAt_properAt_of_injAt (h : k2Karoubi_InjAt s) : k2KarInjAt_ProperAt s :=
  fun _ _ ↦ h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInjAt_properAt_of_injAt

end KarInjAtStatement

end GroupApproximation.BooneHigman.Metabelian.ElemFP
