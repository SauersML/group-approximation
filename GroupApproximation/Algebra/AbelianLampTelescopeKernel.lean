import GroupApproximation.Algebra.AbelianLampPushforward
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# The limit kernel of a pushforward tower is the union of the stage kernels

The arithmetic half of **Theorem 37.5**.  `AbelianLampPushforward` gives the
tower of pushforwards and the monotonicity of their kernels; what remains is the
identification

    ker (push q∞) = ⨆ n, ker (push qₙ)

under the hypothesis that makes the ascending-HNN telescope work: every *finite*
set of sites is separated at some finite stage exactly as it is at the limit.
In the application the sites are cosets `G/Γ₀`, the stages are `G/Γₙ`, the limit
is `G/N` with `N = ⋃ Γₙ`, and the hypothesis holds because a finitely supported
configuration has finitely many support sites, so the finitely many coincidences
`gᵢ⁻¹gⱼ ∈ N` all occur inside a single `Γₙ`.

The inclusion that needs work is `⊆`.  It is a fibre computation: the value of
a pushforward at a target site is the sum over the fibre met by the support, and
under the separation hypothesis the stage-`n` fibre and the limit fibre cut the
support in the same set.
-/

namespace GroupApproximation
namespace AbLamp

universe u v w

variable {A : Type u} [AddCommGroup A] {X : Type v}

open Classical in
/-- The value of a pushforward at a site is the sum of the source values over
the part of the fibre that meets the support. -/
theorem mapDomain_apply_eq_sum {Y : Type w} (q : X → Y) (v : X →₀ A) (b : Y) :
    Finsupp.mapDomain q v b
      = ∑ x ∈ v.support.filter (fun x => q x = b), v x := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.single_apply]

open Classical in
/-- **Theorem 37.5, the union step.** -/
theorem ker_push_eq_iSup {Y : ℕ → Type w} {Z : Type w}
    (q : ∀ n, X → Y n) (qinf : X → Z)
    (hfac : ∀ n, ∃ p : Y n → Z, qinf = p ∘ q n)
    (hsep : ∀ S : Finset X, ∃ n, ∀ x ∈ S, ∀ y ∈ S, qinf x = qinf y → q n x = q n y) :
    (push (A := A) qinf).ker = ⨆ n, (push (A := A) (q n)).ker := by
  classical
  refine le_antisymm ?_ ?_
  · -- Every limit-invisible configuration is already invisible at some stage.
    intro f hf
    rw [MonoidHom.mem_ker] at hf
    set v : X →₀ A := Multiplicative.toAdd f with hv
    have hzeroinf : Finsupp.mapDomain qinf v = 0 := by
      have := congrArg Multiplicative.toAdd hf
      simpa [hv] using this
    obtain ⟨n, hn⟩ := hsep v.support
    obtain ⟨p, hp⟩ := hfac n
    have hzero : Finsupp.mapDomain (q n) v = 0 := by
      refine Finsupp.ext fun b => ?_
      rw [mapDomain_apply_eq_sum, Finsupp.coe_zero, Pi.zero_apply]
      by_cases hb : ∃ x₀ ∈ v.support, q n x₀ = b
      · obtain ⟨x₀, hx₀mem, hx₀⟩ := hb
        have hfilter :
            v.support.filter (fun x => q n x = b)
              = v.support.filter (fun x => qinf x = qinf x₀) := by
          refine Finset.filter_congr fun x hx => ?_
          constructor
          · intro hqx
            have : q n x = q n x₀ := by rw [hqx, hx₀]
            rw [hp]
            exact congrArg p this
          · intro hqx
            have := hn x hx x₀ hx₀mem hqx
            rw [this, hx₀]
        have hsum : ∑ x ∈ v.support.filter (fun x => qinf x = qinf x₀), v x = 0 := by
          have := congrArg (fun g : Z →₀ A => g (qinf x₀)) hzeroinf
          simpa [mapDomain_apply_eq_sum] using this
        rw [hfilter]
        exact hsum
      · push Not at hb
        refine Finset.sum_eq_zero ?_
        intro x hx
        rw [Finset.mem_filter] at hx
        exact absurd hx.2 (hb x hx.1)
    have hmem : f ∈ (push (A := A) (q n)).ker := by
      rw [MonoidHom.mem_ker]
      have hval : push (A := A) (q n) f
          = Multiplicative.ofAdd (Finsupp.mapDomain (q n) v) := rfl
      rw [hval, hzero, ofAdd_zero]
    exact Subgroup.mem_iSup_of_mem n hmem
  · -- Each stage kernel is contained in the limit kernel.
    refine iSup_le fun n => ?_
    obtain ⟨p, hp⟩ := hfac n
    have : (push (A := A) qinf) = (push (A := A) p).comp (push (A := A) (q n)) := by
      rw [hp, push_comp]
    intro f hf
    rw [MonoidHom.mem_ker] at hf ⊢
    rw [this, MonoidHom.comp_apply, hf, map_one]

end AbLamp
end GroupApproximation
