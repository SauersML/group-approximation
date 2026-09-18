import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoeffGap
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModIface
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModRedNorm
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModRedFin
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModRedArt
import GroupApproximation.BooneHigman.GroupRing.Noetherian
import GroupApproximation.BooneHigman.Primary.Coprimary
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.BigOperators.Pi
import GroupApproximation.Meta.AxiomGuard

/-!
# The module side from the `D`-interface (bh-met-87g, assembly)

**Target.** `EHighWittCoeffModuleStatement` (`PureCharPrimeEHighWittCoeffGap.lean`), reduced to
the two pure `D`-statements of `PureCharPrimeEHighWittModIface.lean`. Steps 1–2 and the
assembly are proved here; steps 3–4 are the hypotheses `hI` and `hE`.

1. `eHighWittModRed_normalization` gives `ψ : D₀ → R` with `ψ S ∩ P = ∅` and `R/P` finite over
   `D₀`. Let `D₀` act on `M` through `ψ`. Since `M` is coprimary, every `s ∈ S` acts
   injectively, so `M → S⁻¹M` (`LocalizedModule`) is injective.
2. `eHighWittModRed_finite` makes `M` finite over `D₀`, so `S⁻¹M` is finite over `D`.
   `D` is Artinian (`eHighWittModRed_isArtinianRing`), so `S⁻¹M` is Artinian.
3. `hE` embeds `S⁻¹M` in `Dˢ`. Each `q` acts `D₀`-linearly on `M`, hence `D`-linearly on
   `S⁻¹M` (`IsLocalizedModule.map` and `extendScalarsOfIsLocalization`). `Dˢ` is injective
   (`hI` and `Module.Injective.pi`), so `ι ∘ q` extends along `ι` to `h q : Dˢ → Dˢ`.
   Take `U q i l = h q (e_l) i`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Endpoint (reduction).** The module side follows from `D` being self-injective and from
the embedding of finitely generated, finite-length `D`-modules into free ones. -/
theorem eHighWittModRed_module_of_iface (hI : EHighWittModSelfInjStatement)
    (hE : EHighWittModEmbedStatement) : EHighWittCoeffModuleStatement := by
  intro p _ Q _ hfg M _ _ hfin P k hM hpP hk _ _
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : IsNoetherianRing (ZMod (p ^ 2)) :=
    _root_.isNoetherian_of_finite (ZMod (p ^ 2)) (ZMod (p ^ 2))
  haveI : Group.FG Q := hfg
  haveI : Module.Finite (MonoidAlgebra (ZMod (p ^ 2)) Q) M := hfin
  haveI : IsNoetherianRing (MonoidAlgebra (ZMod (p ^ 2)) Q) :=
    GroupRing.isNoetherianRing_monoidAlgebra
  haveI : P.IsPrime := hM.isPrime
  obtain ⟨d, ψ, hS, hψ⟩ := eHighWittModRed_normalization p Q P hpP
  letI : Module (MvPolynomial (Fin d) (ZMod (p ^ 2))) M := Module.compHom M ψ
  haveI : Module.Finite (MvPolynomial (Fin d) (ZMod (p ^ 2))) M :=
    eHighWittModRed_finite ψ (fun _ _ => rfl) P hψ k (by omega) hM.smul_eq_zero_of_mem_pow
  haveI : IsArtinianRing (eHighWittCoeff_D p (Fin d)) := eHighWittModRed_isArtinianRing p d
  obtain ⟨s, ι, hι⟩ := hE p d (LocalizedModule (eHighWittCoeff_S p (Fin d)) M)
    inferInstance inferInstance
  haveI : Module.Injective (eHighWittCoeff_D p (Fin d)) (eHighWittCoeff_D p (Fin d)) := hI p d
  haveI : Module.Injective (eHighWittCoeff_D p (Fin d)) (Fin s → eHighWittCoeff_D p (Fin d)) :=
    Module.Injective.pi (eHighWittCoeff_D p (Fin d)) (fun _ : Fin s => eHighWittCoeff_D p (Fin d))
  let T0 : Q → M →ₗ[MvPolynomial (Fin d) (ZMod (p ^ 2))] M := fun q =>
    { toFun := fun m => MonoidAlgebra.of (ZMod (p ^ 2)) Q q • m
      map_add' := fun x y => smul_add (MonoidAlgebra.of (ZMod (p ^ 2)) Q q) x y
      map_smul' := fun a m => by
        show MonoidAlgebra.of (ZMod (p ^ 2)) Q q • (ψ a • m) =
          ψ a • (MonoidAlgebra.of (ZMod (p ^ 2)) Q q • m)
        rw [← mul_smul, mul_comm, mul_smul] }
  let Tq : Q → LocalizedModule (eHighWittCoeff_S p (Fin d)) M →ₗ[eHighWittCoeff_D p (Fin d)]
      LocalizedModule (eHighWittCoeff_S p (Fin d)) M := fun q =>
    (IsLocalizedModule.map (eHighWittCoeff_S p (Fin d))
      (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M)
      (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M)
      (T0 q)).extendScalarsOfIsLocalization (eHighWittCoeff_S p (Fin d))
        (eHighWittCoeff_D p (Fin d))
  have hTq : ∀ (q : Q) (m : M),
      Tq q (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M m) =
        LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M
          (MonoidAlgebra.of (ZMod (p ^ 2)) Q q • m) := fun q m =>
    IsLocalizedModule.map_apply (eHighWittCoeff_S p (Fin d))
      (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M)
      (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M) (T0 q) m
  have hext : ∀ q : Q, ∃ h : (Fin s → eHighWittCoeff_D p (Fin d)) →ₗ[eHighWittCoeff_D p (Fin d)]
      (Fin s → eHighWittCoeff_D p (Fin d)), ∀ n, h (ι n) = ι (Tq q n) := fun q =>
    Module.Injective.out ι hι (ι ∘ₗ Tq q)
  choose h hh using hext
  refine ⟨d, s, ι.toAddMonoidHom.comp
    (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M).toAddMonoidHom,
    fun q i l => h q (fun j => if l = j then 1 else 0) i, ?_, ?_⟩
  · have hmk : Function.Injective
        (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M) := by
      refine (injective_iff_map_eq_zero _).mpr fun m hm => ?_
      obtain ⟨r, hr, hrm⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp (LinearMap.mem_ker.mpr hm)
      exact hM.smul_injective_of_notMem (ψ r) (hS r hr) (a₁ := m) (a₂ := 0)
        (show ψ r • m = ψ r • (0 : M) by rw [smul_zero]; exact hrm)
    intro a b hab
    have hab' : ι (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M a) =
        ι (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M b) := hab
    exact hmk (hι hab')
  · intro q m i
    show ι (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M
        (MonoidAlgebra.of (ZMod (p ^ 2)) Q q • m)) i =
      ∑ l : Fin s, h q (fun j => if l = j then 1 else 0) i *
        ι (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M m) l
    have h1 : ι (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M
        (MonoidAlgebra.of (ZMod (p ^ 2)) Q q • m)) =
          h q (ι (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M m)) :=
      ((hh q (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M m)).trans
        (congrArg ι (hTq q m))).symm
    rw [h1, LinearMap.pi_apply_eq_sum_univ (h q)
      (ι (LocalizedModule.mkLinearMap (eHighWittCoeff_S p (Fin d)) M m))]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModRed_module_of_iface

end GroupApproximation.BooneHigman.Metabelian.Coprimary
