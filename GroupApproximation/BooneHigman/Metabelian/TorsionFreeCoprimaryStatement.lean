import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import GroupApproximation.BooneHigman.Primary.Coprimary
import GroupApproximation.BooneHigman.Metabelian.PureCharZeroStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Torsion-free linearity: the coprimary statement (lane bh-met-42)

`TorsionFreeModuleLinearityStatement` (`PureCharZeroStatement`) asks: a finitely generated
`ℤ[Q]`-module `W` (`Q` a finitely generated commutative group) that is torsion-free as an abelian
group embeds `Q`-equivariantly into `K^d` for a field `K` of characteristic zero.

This lane reduces it to the same conclusion for **coprimary** modules only
(`CoprimaryTorsionFreeLinearityStatement`): the extra hypothesis is that `W` is coprimary with some
prime `P` and exponent `e` (`Primary.IsCoprimaryWith`).  The smaller statement is strictly weaker in
logical strength (one more hypothesis, same conclusion).  It is true: `W ↪ W_P`, and `W_P` is a
module of finite length over the Artinian local ring `ℤ[Q]_P / P^e`, whose residue field has
characteristic zero (`P ∩ ℤ = 0` as `W` is torsion-free), so it has a coefficient field `L`, and
`W_P` is a finite-dimensional `L`-vector space on which `Q` acts `L`-linearly.

This file holds the statement and the module-theoretic part of the reduction:

* `isAddTorsionFree_of_zsmul_injective`: integer multiplications injective gives torsion-free.
* `eq_zero_of_mem_torsionFree_pieces`: in a coprimary decomposition `0 = S_1 ∩ ... ∩ S_n` of a
  torsion-free module, the pieces `S_i` with torsion-free quotient already meet in `0`.  The other
  quotients are killed by a nonzero integer `c_i` (`torsionFree_or_primeExponent`), so for `w` in
  every torsion-free piece, `(∏ c_i) • w` lies in every `S_i`, hence is `0`, hence `w = 0`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- The torsion-free linearity statement restricted to **coprimary** modules. -/
def CoprimaryTorsionFreeLinearityStatement : Prop :=
  ∀ (Q : Type) [CommGroup Q], Group.FG Q → ∀ (W : Type) [AddCommGroup W]
    [Module (MonoidAlgebra ℤ Q) W], Module.Finite (MonoidAlgebra ℤ Q) W → IsAddTorsionFree W →
    ∀ (P : Ideal (MonoidAlgebra ℤ Q)) (e : ℕ), Primary.IsCoprimaryWith (MonoidAlgebra ℤ Q) W P e →
    ∃ (K : Type) (_ : Field K) (d : ℕ) (ρ : Q →* Matrix.GeneralLinearGroup (Fin d) K)
      (ι : W →+ (Fin d → K)), ringChar K = 0 ∧ Function.Injective ι ∧
      ∀ (q : Q) (w : W), ι (MonoidAlgebra.of ℤ Q q • w) =
        Matrix.mulVec (ρ q : Matrix (Fin d) (Fin d) K) (ι w)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.CoprimaryTorsionFreeLinearityStatement

/-- If every nonzero integer acts injectively, the group is torsion-free. -/
theorem isAddTorsionFree_of_zsmul_injective {M : Type*} [AddCommGroup M]
    (h : ∀ n : ℤ, n ≠ 0 → Function.Injective fun x : M => n • x) : IsAddTorsionFree M :=
  ⟨fun k hk a b hab => h k (by exact_mod_cast hk) (by simpa only [natCast_zsmul] using hab)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.isAddTorsionFree_of_zsmul_injective

/-- Each coprimary piece has a nonzero integer `c` with `c • x ∈ S` for all `x` that must lie in
`S` when the quotient is torsion-free. -/
theorem exists_int_smul_mem_piece {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (S : Submodule R W) {P : Ideal R} {e : ℕ} (hP : Primary.IsCoprimaryWith R (W ⧸ S) P e) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ x : W, (IsAddTorsionFree (W ⧸ S) → x ∈ S) → c • x ∈ S := by
  rcases hP.torsionFree_or_primeExponent with h0 | ⟨p, hp, -, hq⟩
  · refine ⟨1, one_ne_zero, fun x hx => ?_⟩
    rw [one_zsmul]
    exact hx (isAddTorsionFree_of_zsmul_injective h0)
  · refine ⟨(p : ℤ) ^ e, pow_ne_zero _ (by exact_mod_cast hp.ne_zero), fun x _ => ?_⟩
    exact (Submodule.Quotient.mk_eq_zero S).mp ((map_zsmul S.mkQ _ x).trans (hq _))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.exists_int_smul_mem_piece

/-- **Torsion-free pieces suffice.** In a coprimary decomposition of a torsion-free module, an
element lying in every piece with torsion-free quotient is `0`. -/
theorem eq_zero_of_mem_torsionFree_pieces {R W : Type*} [CommRing R] [AddCommGroup W]
    [Module R W] [IsAddTorsionFree W] {n : ℕ} (S : Fin n → Submodule R W)
    {P : Fin n → Ideal R} {e : Fin n → ℕ} (hS : ∀ m : W, (∀ i, m ∈ S i) → m = 0)
    (hP : ∀ i, Primary.IsCoprimaryWith R (W ⧸ S i) (P i) (e i)) (w : W)
    (hw : ∀ i, IsAddTorsionFree (W ⧸ S i) → w ∈ S i) : w = 0 := by
  choose c hc0 hcS using fun i => exists_int_smul_mem_piece (S i) (hP i)
  have hN : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hc0 i
  have hmem : ∀ i, (∏ j, c j) • w ∈ S i := by
    intro i
    rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i), mul_zsmul]
    exact hcS i _ fun hg => zsmul_mem (hw i hg) _
  have h0 : (∏ j, c j) • w = (∏ j, c j) • (0 : W) := by
    rw [zsmul_zero]
    exact hS _ hmem
  exact zsmul_right_injective hN h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eq_zero_of_mem_torsionFree_pieces

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
