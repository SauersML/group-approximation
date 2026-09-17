import GroupApproximation.BooneHigman.Metabelian.ChainHost
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain skeleton, part 3: linear groups in characteristic zero

Research node `char-zero-linear-groups-satisfy-permutational-boone-higman`, route
`char-zero-linear-pbh-via-polynomial-self-similar-hosts`.  With
`S_{m,k} = ℤ[1/m][t_0, ..., t_{k-1}]`:

1. (`CharZeroPolynomialCoordinatesStatement`, research node
   `char-zero-linear-groups-embed-in-polynomial-s-integer-groups`, lane `bh-met-09`) a finitely
   generated `H ≤ GL_n(K)`, `char K = 0`, embeds in `GL_M(S_{m,k})`;
2. (`CharZeroElementaryAbsorptionStatement`, no owning lane) `GL_M(S) ↪ E_N(S)` for `N ≥ 3`,
   `N ≥ 2M`, through `g ↦ diag(g, g⁻ᵀ, 1)` and `SL_N(S_{m,k}) = E_N(S_{m,k})` (Suslin);
3. (`CharZeroElementaryFPStatement`, research node
   `elementary-groups-over-polynomial-s-integers-are-fp`, no owning lane) `E_N(S_{m,k})` is finitely
   presented for `N ≥ k + 4`;
4. (`AffineExtensionFPStatement`, lane `bh-met-05`, in `ChainHost.lean`) the affine host is finitely
   presented;
5. (`CharZeroAffineSelfSimilarStatement`, research node
   `polynomial-parameter-affine-groups-are-self-similar`, lane `bh-met-09`) the affine host over
   `S_{m,k}` acts faithfully and self-similarly on a regular rooted tree.

As in `ChainCharP.lean`, the class `B_A` is replaced by `Products.EmbedsInFPSelfSimilarGroup`.
Endpoint: `charZeroLinearHostStatement_of_chain`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- The polynomial ring `ℤ[1/m][t_0, ..., t_{k-1}]` over the `S`-integers `ℤ[1/m]`. -/
abbrev SIntPoly (m k : ℕ) : Type := MvPolynomial (Fin k) (Localization.Away (m : ℤ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.SIntPoly

/-- **Research node `char-zero-linear-groups-embed-in-polynomial-s-integer-groups`** (lane
`bh-met-09`; restated here since no such interface was on disk): every finitely generated subgroup
of `GL_n(K)`, `char K = 0`, embeds in `GL_M(ℤ[1/m][t_0, ..., t_{k-1}])` for some `m, k, M`. -/
def CharZeroPolynomialCoordinatesStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)), H.FG →
      ∃ (m k M : ℕ) (ψ : H →* Matrix.GeneralLinearGroup (Fin M) (SIntPoly m k)),
        Function.Injective ψ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharZeroPolynomialCoordinatesStatement

/-- **Absorption into the elementary group** (no owning lane).  For `N ≥ 3` and `N ≥ 2M`,
`GL_M(S_{m,k})` embeds in `E_N(S_{m,k})`: `g ↦ diag(g, g⁻ᵀ, 1)` lands in `SL_N`, and
`SL_N(ℤ[1/m][t]) = E_N` for `N ≥ 3` (Suslin; `K_1` homotopy invariance for the regular ring
`ℤ[1/m]`, which is a PID; for `m = 0` the ring is zero). -/
def CharZeroElementaryAbsorptionStatement : Prop :=
  ∀ (m k M N : ℕ), 3 ≤ N → 2 * M ≤ N →
    ∃ f : Matrix.GeneralLinearGroup (Fin M) (SIntPoly m k) →*
        elementaryGroup (Fin N) (SIntPoly m k),
      Function.Injective f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharZeroElementaryAbsorptionStatement

/-- **Research node `elementary-groups-over-polynomial-s-integers-are-fp`** (no owning lane):
`E_N(ℤ[1/m][t_0, ..., t_{k-1}])` is finitely presented for `N ≥ k + 4`. -/
def CharZeroElementaryFPStatement : Prop :=
  ∀ (m k N : ℕ), k + 4 ≤ N →
    Group.IsFinitelyPresented (elementaryGroup (Fin N) (SIntPoly m k))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharZeroElementaryFPStatement

/-- **Research node `polynomial-parameter-affine-groups-are-self-similar`** (lane `bh-met-09`;
restated here since no such interface was on disk): for `n ≥ 1` the affine host
`S_{m,k}^n ⋊ E_n(S_{m,k})` acts faithfully and self-similarly on the tree over a finite alphabet
with at least two letters (states `t_j ↦ a_j + p t_j` for a prime `p ∤ m`). -/
def CharZeroAffineSelfSimilarStatement : Prop :=
  ∀ (m k n : ℕ), 1 ≤ n →
    ∃ (X : Type) (_ : Finite X) (_ : Nontrivial X)
      (ρ : AffineElementaryGroup n (SIntPoly m k) →* Trees.TreeAut X), Trees.IsSelfSimilarRep ρ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharZeroAffineSelfSimilarStatement

/-- **Research node `char-zero-linear-groups-satisfy-permutational-boone-higman`**, with `B_A`
replaced by `Products.EmbedsInFPSelfSimilarGroup`. -/
def CharZeroLinearHostStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)), H.FG →
      Products.EmbedsInFPSelfSimilarGroup H

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CharZeroLinearHostStatement

/-- `ℤ[1/m][t_0, ..., t_{k-1}]` is a finitely generated `ℤ`-algebra. -/
theorem sIntPoly_finiteType (m k : ℕ) : Algebra.FiniteType ℤ (SIntPoly m k) := by
  haveI : Algebra.FinitePresentation ℤ (Localization.Away (m : ℤ)) :=
    IsLocalization.Away.finitePresentation (m : ℤ)
  infer_instance

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.sIntPoly_finiteType

/-- **Composition for the characteristic-zero node.** -/
theorem charZeroLinearHostStatement_of_chain
    (hcoord : CharZeroPolynomialCoordinatesStatement)
    (habs : CharZeroElementaryAbsorptionStatement) (hfp : CharZeroElementaryFPStatement)
    (haff : AffineExtensionFPStatement) (hss : CharZeroAffineSelfSimilarStatement) :
    CharZeroLinearHostStatement := by
  intro K _ _ n H hH
  obtain ⟨m, k, M, ψ, hψ⟩ := hcoord K n H hH
  obtain ⟨f, hf⟩ := habs m k M (k + 4 + 2 * M) (by omega) (by omega)
  have hE : Group.IsFinitelyPresented
      (elementaryGroup (Fin (k + 4 + 2 * M)) (SIntPoly m k)) :=
    hfp m k (k + 4 + 2 * M) (by omega)
  haveI : Group.IsFinitelyPresented (AffineElementaryGroup (k + 4 + 2 * M) (SIntPoly m k)) :=
    haff (SIntPoly m k) (finiteType_int_transfer _ (sIntPoly_finiteType m k) _)
      (k + 4 + 2 * M) (by omega) hE
  obtain ⟨X, _, _, ρ, hρ⟩ := hss m k (k + 4 + 2 * M) (by omega)
  exact embedsInFPSelfSimilarGroup_of_affineHost (X := X) ρ hρ (f := f.comp ψ) (hf.comp hψ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.charZeroLinearHostStatement_of_chain

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
