import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModInjBaer
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Fin.Tuple.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Artinian `D`-modules embed in `Dˢ` (bh-met-87f, part 4)

This proves `EHighWittModEmbedStatement` (`PureCharPrimeEHighWittModIface.lean`), using only
that `D = ZMod (p²)[σ]_(p)` is self-injective (`eHighWittModInj_selfInj`). In fact the
statement holds for every Artinian `D`-module; its `Module.Finite` hypothesis is not needed.

* `eHighWittModInj_exists_ne_zero`: for `n ≠ 0` in a `D`-module `N` there is a linear
  `f : N → D` with `f n ≠ 0`. Let `K = ann(n)`. Every `r ∈ K` has `r p = 0`, because either
  `r` is a unit (then `n = 0`) or `r ∈ pD` (then `r p ∈ p²D = 0`). So `r ↦ r p` factors
  through `D ⧸ K ≅ D n ⊆ N`, and self-injectivity extends it to `f : N → D`
  with `f n = p ≠ 0`.
* `eHighWittModInj_embed_of_artinian`: choose a minimal kernel `ker (f₁, …, fₛ)` among all
  finite families of maps `N → D` (the module is Artinian). If `x ≠ 0` were in it, a map `g`
  with `g x ≠ 0` would give the strictly smaller kernel `ker (g, f₁, …, fₛ)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

variable (p : ℕ) (σ : Type)

/-- **Linear functionals `N → D` separate points** (`D` self-injective, `p ≠ 0`, `p² = 0`). -/
theorem eHighWittModInj_exists_ne_zero [Fact p.Prime] {N : Type} [AddCommGroup N]
    [Module (eHighWittCoeff_D p σ) N] {n : N} (hn : n ≠ 0) :
    ∃ f : N →ₗ[eHighWittCoeff_D p σ] eHighWittCoeff_D p σ, f n ≠ 0 := by
  have hK : LinearMap.ker (LinearMap.toSpanSingleton (eHighWittCoeff_D p σ) N n) ≤
      LinearMap.ker (LinearMap.toSpanSingleton (eHighWittCoeff_D p σ) (eHighWittCoeff_D p σ)
        ((p : ℕ) : eHighWittCoeff_D p σ)) := by
    intro r hr
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hr ⊢
    rw [smul_eq_mul]
    rcases eHighWittModInj_isUnit_or p σ r with ⟨u, rfl⟩ | ⟨w, rfl⟩
    · exact (hn (by
        rw [← one_smul (eHighWittCoeff_D p σ) n, ← Units.inv_mul u, mul_smul, hr,
          smul_zero])).elim
    · rw [mul_right_comm, eHighWittModInj_p_mul_p p σ, zero_mul]
  obtain ⟨h, hh⟩ := (eHighWittModInj_selfInj p σ).out
    ((LinearMap.ker (LinearMap.toSpanSingleton (eHighWittCoeff_D p σ) N n)).liftQ
      (LinearMap.toSpanSingleton (eHighWittCoeff_D p σ) N n) le_rfl)
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))
    ((LinearMap.ker (LinearMap.toSpanSingleton (eHighWittCoeff_D p σ) N n)).liftQ
      (LinearMap.toSpanSingleton (eHighWittCoeff_D p σ) (eHighWittCoeff_D p σ)
        ((p : ℕ) : eHighWittCoeff_D p σ)) hK)
  have h3 := hh (Submodule.Quotient.mk 1)
  simp only [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul] at h3
  exact ⟨h, by rw [h3]; exact eHighWittModInj_p_ne_zero p σ⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_exists_ne_zero

/-- **Every Artinian `D`-module embeds `D`-linearly in some `Dˢ`.** -/
theorem eHighWittModInj_embed_of_artinian [Fact p.Prime] {N : Type} [AddCommGroup N]
    [Module (eHighWittCoeff_D p σ) N] (hA : IsArtinian (eHighWittCoeff_D p σ) N) :
    ∃ (s : ℕ) (ι : N →ₗ[eHighWittCoeff_D p σ] (Fin s → eHighWittCoeff_D p σ)),
      Function.Injective ι := by
  obtain ⟨K, ⟨s, fs, rfl⟩, hmin⟩ := (set_has_minimal_iff_artinian.mpr hA)
    {K : Submodule (eHighWittCoeff_D p σ) N | ∃ (s : ℕ)
      (fs : Fin s → (N →ₗ[eHighWittCoeff_D p σ] eHighWittCoeff_D p σ)),
      K = LinearMap.ker (LinearMap.pi fs)}
    ⟨_, 0, Fin.elim0, rfl⟩
  refine ⟨s, LinearMap.pi fs,
    LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx => ?_)⟩
  by_contra hne
  obtain ⟨g, hg⟩ := eHighWittModInj_exists_ne_zero p σ hne
  have hle : LinearMap.ker (LinearMap.pi
      (Fin.cons g fs : Fin (s + 1) → (N →ₗ[eHighWittCoeff_D p σ] eHighWittCoeff_D p σ))) ≤
      LinearMap.ker (LinearMap.pi fs) := by
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    funext i
    simpa only [LinearMap.pi_apply, Fin.cons_succ, Pi.zero_apply] using congrFun hy i.succ
  have heq := eq_of_le_of_not_lt hle (hmin _ ⟨s + 1, Fin.cons g fs, rfl⟩)
  have hx' : x ∈ LinearMap.ker (LinearMap.pi
      (Fin.cons g fs : Fin (s + 1) → (N →ₗ[eHighWittCoeff_D p σ] eHighWittCoeff_D p σ))) :=
      by
    rw [heq]
    exact LinearMap.mem_ker.mpr hx
  rw [LinearMap.mem_ker] at hx'
  apply hg
  simpa only [LinearMap.pi_apply, Fin.cons_zero, Pi.zero_apply] using congrFun hx' 0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_embed_of_artinian

/-- **Endpoint: `EHighWittModEmbedStatement` holds** (the `Module.Finite` hypothesis is unused). -/
theorem eHighWittModInj_embedStatement : EHighWittModEmbedStatement := by
  intro p _ d N _ _ _ hA
  exact eHighWittModInj_embed_of_artinian p (Fin d) hA

#audit_closed_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModInj_embedStatement

end GroupApproximation.BooneHigman.Metabelian.Coprimary
