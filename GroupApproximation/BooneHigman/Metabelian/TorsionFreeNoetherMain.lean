import Mathlib.RingTheory.FiniteType
import GroupApproximation.BooneHigman.Metabelian.AffineFPPresentation
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryStatement
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeNoetherLocalize
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeNoetherMatrix
import GroupApproximation.Meta.AxiomGuard

/-!
# Torsion-free linearity, coprimary case: the endpoint (lane bh-met-43)

Proof of `CoprimaryTorsionFreeLinearityStatement` (lane bh-met-42's statement).

* `P ∩ ℤ = 0`: if a nonzero integer `n` lies in `P`, then `n^e ∈ P^e` kills `W`, but `W` is
  nontrivial and torsion-free (`noether_int_notMem`).
* `ℤ[Q]` is a finitely generated ring (`MonoidAlgebra.finiteType_of_fg`), so it has a finite set
  of ring generators (`AffineFP.exists_finite_ring_generators`).
* Generic localization (`noether_exists_fd_embedding`) gives a `Q`-equivariant embedding into a
  finite-dimensional vector space over a field of characteristic zero, and choosing a basis gives
  matrices (`noether_exists_matrix_rep`).

* `coprimaryTorsionFreeLinearity`: the endpoint.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- A coprimary torsion-free module has a prime containing no nonzero integer. -/
theorem noether_int_notMem {A W : Type} [CommRing A] [AddCommGroup W] [Module A W]
    [IsAddTorsionFree W] {P : Ideal A} {e : ℕ} (hW : Primary.IsCoprimaryWith A W P e) :
    ∀ n : ℤ, n ≠ 0 → (n : A) ∉ P := by
  intro n hn hnP
  haveI := hW.nontrivial
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  apply hw
  refine zsmul_right_injective (pow_ne_zero e hn) ?_
  show (n ^ e) • w = (n ^ e) • (0 : W)
  rw [zsmul_zero, ← Int.cast_smul_eq_zsmul A, Int.cast_pow]
  exact hW.smul_eq_zero_of_mem_pow _ (Ideal.pow_mem_pow hnP e) w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.noether_int_notMem

/-- **Lane bh-met-43.** Coprimary torsion-free modules over `ℤ[Q]` are linear over a field of
characteristic zero. -/
theorem coprimaryTorsionFreeLinearity : CoprimaryTorsionFreeLinearityStatement := by
  intro Q _ hQ W _ _ hWf hTF P e hW
  haveI : Group.FG Q := hQ
  haveI : Module.Finite (MonoidAlgebra ℤ Q) W := hWf
  haveI : IsAddTorsionFree W := hTF
  have key : ∀ inst : Algebra ℤ (MonoidAlgebra ℤ Q),
      @Algebra.FiniteType ℤ (MonoidAlgebra ℤ Q) _ _ inst := by
    intro inst
    obtain rfl : inst = MonoidAlgebra.algebra := Subsingleton.elim _ _
    exact MonoidAlgebra.finiteType_of_fg
  obtain ⟨t, ht, -, hcl⟩ :=
    @AffineFP.exists_finite_ring_generators (MonoidAlgebra ℤ Q) _ (key _)
  obtain ⟨K, _, V, _, _, hK, hfd, τ, ι₀, hι₀, hτ⟩ :=
    noether_exists_fd_embedding t ht hcl P e hW (noether_int_notMem hW)
  haveI := hfd
  exact noether_exists_matrix_rep hK (τ.comp (MonoidAlgebra.of ℤ Q)) ι₀ hι₀
    (fun q w => hτ (MonoidAlgebra.of ℤ Q q) w)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.coprimaryTorsionFreeLinearity

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
