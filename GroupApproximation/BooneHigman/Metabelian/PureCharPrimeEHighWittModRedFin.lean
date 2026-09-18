import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Lemmas
import GroupApproximation.Meta.AxiomGuard

/-!
# Descending finiteness along `ψ` (bh-met-87g, part 2)

Let `ψ : A → R` be a ring map with `R` Noetherian, and let `M` be a finite `R`-module on which
`A` acts through `ψ`. Suppose `P^k` kills `M` (`k ≠ 0`) and `R/P` is finite over `A`. Then `M`
is a finite `A`-module:
* `R/P^k → R/P` is surjective with nilpotent, finitely generated kernel `P/P^k`. So
  `R/P^k` is finite over `A` (`Module.finite_of_surjective_of_ker_le_nilradical`).
* `M` is a finite `R/P^k`-module, and `A → R/P^k` is finite, so `M` is finite over `A`.

This is step 2 of the paper route, done without any filtration by `P^i`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Finiteness over `A`.** A finite `R`-module killed by `P^k` is finite over `A` once `R/P` is
finite over `A` along `ψ`. -/
theorem eHighWittModRed_finite {A R M : Type*} [CommRing A] [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module A M] [Module.Finite R M]
    (ψ : A →+* R) (hsmul : ∀ (a : A) (x : M), a • x = ψ a • x)
    (P : Ideal R) (hψ : ((Ideal.Quotient.mk P).comp ψ).Finite) (k : ℕ) (hk : k ≠ 0)
    (hM : ∀ r ∈ P ^ k, ∀ x : M, r • x = 0) : Module.Finite A M := by
  letI : Algebra A R := ψ.toAlgebra
  haveI : IsScalarTower A R M := ⟨fun a r x => by
    show (ψ a * r) • x = a • (r • x)
    rw [mul_smul, hsmul]⟩
  have hψ' : (algebraMap A (R ⧸ P)).Finite := hψ
  haveI : Module.Finite A (R ⧸ P) := RingHom.finite_algebraMap.mp hψ'
  have hle : P ^ k ≤ P := Ideal.pow_le_self hk
  have hsurj : Function.Surjective (Ideal.Quotient.factorₐ A hle) := fun y => by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk (P ^ k) z, rfl⟩
  have hnil : RingHom.ker (Ideal.Quotient.factorₐ A hle) ≤ nilradical (R ⧸ P ^ k) := by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker] at hy
    have hy' : Ideal.Quotient.mk P z = 0 := hy
    have hz : z ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hy'
    refine mem_nilradical.mpr ⟨k, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hz k
  haveI : Module.Finite A (R ⧸ P ^ k) :=
    Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.factorₐ A hle) hsurj hnil
      (IsNoetherian.noetherian _)
  have hT : Module.IsTorsionBySet R M (P ^ k : Ideal R) := fun x a => hM a.1 a.2 x
  letI : Module (R ⧸ P ^ k) M := Module.IsTorsionBySet.module hT
  have hmk : ∀ (r : R) (x : M), Ideal.Quotient.mk (P ^ k) r • x = r • x := fun _ _ => rfl
  haveI : IsScalarTower R (R ⧸ P ^ k) M := ⟨fun r y x => by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (smul_assoc r z x :)⟩
  haveI : IsScalarTower A (R ⧸ P ^ k) M := ⟨fun a y x => by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Algebra.smul_def a (Ideal.Quotient.mk (P ^ k) z)]
    show (Ideal.Quotient.mk (P ^ k) (ψ a) * Ideal.Quotient.mk (P ^ k) z) • x =
      a • (Ideal.Quotient.mk (P ^ k) z • x)
    rw [← map_mul, hmk, hmk, hsmul, mul_smul]⟩
  haveI : Module.Finite (R ⧸ P ^ k) M := Module.Finite.of_restrictScalars_finite R (R ⧸ P ^ k) M
  exact Module.Finite.trans (R ⧸ P ^ k) M

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModRed_finite

end GroupApproximation.BooneHigman.Metabelian.Coprimary
