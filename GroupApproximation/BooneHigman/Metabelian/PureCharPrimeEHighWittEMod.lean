import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittENorm
import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittModRedFin
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
# The module side over `D_e = ZMod (p ^ e)[X₁..X_d]_(p)` (bh-met-87h, part 4)

This is `eHighWittModRed_module_of_iface` with `p²` replaced by `p ^ e`. The two interface
hypotheses of that file are now proved for every `e` by the chain-ring lemmas of
`PureCharPrimeEHighWittEChain.lean`, using `eHighWittE_isChain`.

A finite coprimary `ZMod (p ^ e)[Q]`-module `M` (prime `P ∋ p`) embeds additively in some
`D_eⁿ`, and each `q ∈ Q` acts there through a matrix `U q` over `D_e`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Module side for all `e`.** A finite coprimary `ZMod (p ^ e)[Q]`-module with `p ∈ P`
embeds in `D_eⁿ` with `Q` acting by matrices. -/
theorem eHighWittE_module (p e : ℕ) [NeZero e] [Fact p.Prime] (Q : Type) [CommGroup Q]
    (hfg : Group.FG Q) (M : Type) [AddCommGroup M]
    [Module (MonoidAlgebra (ZMod (p ^ e)) Q) M]
    (hfin : Module.Finite (MonoidAlgebra (ZMod (p ^ e)) Q) M)
    (P : Ideal (MonoidAlgebra (ZMod (p ^ e)) Q)) (k : ℕ)
    (hM : Primary.IsCoprimaryWith (MonoidAlgebra (ZMod (p ^ e)) Q) M P k)
    (hpP : ((p : ℕ) : MonoidAlgebra (ZMod (p ^ e)) Q) ∈ P) (hk : k ≠ 0) :
    ∃ (d n : ℕ) (j : M →+ (Fin n → eHighWittE_D p e (Fin d)))
      (U : Q → Fin n → Fin n → eHighWittE_D p e (Fin d)),
      Function.Injective j ∧
      ∀ (q : Q) (m : M) (i : Fin n),
        j (MonoidAlgebra.of (ZMod (p ^ e)) Q q • m) i = ∑ l, U q i l * j m l := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  haveI : IsNoetherianRing (ZMod (p ^ e)) :=
    _root_.isNoetherian_of_finite (ZMod (p ^ e)) (ZMod (p ^ e))
  haveI : Group.FG Q := hfg
  haveI : Module.Finite (MonoidAlgebra (ZMod (p ^ e)) Q) M := hfin
  haveI : IsNoetherianRing (MonoidAlgebra (ZMod (p ^ e)) Q) :=
    GroupRing.isNoetherianRing_monoidAlgebra
  haveI : P.IsPrime := hM.isPrime
  obtain ⟨d, ψ, hS, hψ⟩ := eHighWittE_normalization p e Q P hpP
  letI : Module (MvPolynomial (Fin d) (ZMod (p ^ e))) M := Module.compHom M ψ
  have hsm : ∀ (a : MvPolynomial (Fin d) (ZMod (p ^ e))) (x : M), a • x = ψ a • x :=
    fun _ _ => rfl
  haveI : Module.Finite (MvPolynomial (Fin d) (ZMod (p ^ e))) M :=
    eHighWittModRed_finite ψ hsm P hψ k hk hM.smul_eq_zero_of_mem_pow
  haveI : IsArtinianRing (eHighWittE_D p e (Fin d)) :=
    eHighWittE_isArtinianRing (eHighWittE_isChain p e (Fin d))
  obtain ⟨s, ι, hι⟩ := eHighWittE_embed_of_artinian (eHighWittE_isChain p e (Fin d))
    (NeZero.ne e) (N := LocalizedModule (eHighWittE_S p e (Fin d)) M) inferInstance
  haveI : Module.Injective (eHighWittE_D p e (Fin d)) (eHighWittE_D p e (Fin d)) :=
    eHighWittE_selfInj (eHighWittE_isChain p e (Fin d))
  haveI : Module.Injective (eHighWittE_D p e (Fin d)) (Fin s → eHighWittE_D p e (Fin d)) :=
    Module.Injective.pi (eHighWittE_D p e (Fin d)) (fun _ : Fin s => eHighWittE_D p e (Fin d))
  let T0 : Q → M →ₗ[MvPolynomial (Fin d) (ZMod (p ^ e))] M := fun q =>
    { toFun := fun m => MonoidAlgebra.of (ZMod (p ^ e)) Q q • m
      map_add' := fun x y => smul_add (MonoidAlgebra.of (ZMod (p ^ e)) Q q) x y
      map_smul' := fun a m => by
        show MonoidAlgebra.of (ZMod (p ^ e)) Q q • (ψ a • m) =
          ψ a • (MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)
        rw [← mul_smul, mul_comm, mul_smul] }
  let Tq : Q → LocalizedModule (eHighWittE_S p e (Fin d)) M →ₗ[eHighWittE_D p e (Fin d)]
      LocalizedModule (eHighWittE_S p e (Fin d)) M := fun q =>
    (IsLocalizedModule.map (eHighWittE_S p e (Fin d))
      (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M)
      (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M)
      (T0 q)).extendScalarsOfIsLocalization (eHighWittE_S p e (Fin d))
        (eHighWittE_D p e (Fin d))
  have hTq : ∀ (q : Q) (m : M),
      Tq q (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M m) =
        LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M
          (MonoidAlgebra.of (ZMod (p ^ e)) Q q • m) := fun q m =>
    IsLocalizedModule.map_apply (eHighWittE_S p e (Fin d))
      (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M)
      (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M) (T0 q) m
  have hext : ∀ q : Q, ∃ h : (Fin s → eHighWittE_D p e (Fin d)) →ₗ[eHighWittE_D p e (Fin d)]
      (Fin s → eHighWittE_D p e (Fin d)), ∀ n, h (ι n) = ι (Tq q n) := fun q =>
    Module.Injective.out ι hι (ι ∘ₗ Tq q)
  choose h hh using hext
  refine ⟨d, s, ι.toAddMonoidHom.comp
    (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M).toAddMonoidHom,
    fun q i l => h q (fun j => if l = j then 1 else 0) i, ?_, ?_⟩
  · have hmk : Function.Injective
        (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M) := by
      refine (injective_iff_map_eq_zero _).mpr fun m hm => ?_
      obtain ⟨r, hr, hrm⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp (LinearMap.mem_ker.mpr hm)
      exact hM.smul_injective_of_notMem (ψ r) (hS r hr) (a₁ := m) (a₂ := 0)
        (show ψ r • m = ψ r • (0 : M) by rw [smul_zero]; exact hrm)
    intro a b hab
    have hab' : ι (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M a) =
        ι (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M b) := hab
    exact hmk (hι hab')
  · intro q m i
    show ι (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M
        (MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)) i =
      ∑ l : Fin s, h q (fun j => if l = j then 1 else 0) i *
        ι (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M m) l
    have h1 : ι (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M
        (MonoidAlgebra.of (ZMod (p ^ e)) Q q • m)) =
          h q (ι (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M m)) :=
      ((hh q (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M m)).trans
        (congrArg ι (hTq q m))).symm
    rw [h1, LinearMap.pi_apply_eq_sum_univ (h q)
      (ι (LocalizedModule.mkLinearMap (eHighWittE_S p e (Fin d)) M m))]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_module

end GroupApproximation.BooneHigman.Metabelian.Coprimary
