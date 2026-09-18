import GroupApproximation.BooneHigman.Coordinates.FGSubring
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsFree
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsAway
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.NoetherNormalization
import GroupApproximation.Meta.AxiomGuard

/-!
# Polynomial coordinates with a transcendence-degree bound (characteristic `p`)

The characteristic-`p` coordinates theorem `CharPCoords.charPPolynomialCoordinates` embeds a
finitely generated `H ≤ GL_n(K)` in `GL_M(F_p[x_0, ..., x_{s-1}])` for some `s`.  Its proof is a
Noether normalization `F_p[x_0, ..., x_{s-1}] ⊆ A` of the finitely generated subalgebra `A ⊆ K`
spanned by the matrix entries, so `s` is at most the transcendence degree of `K` over `F_p`.
This module records that bound:

* `exists_polynomialCoordinates_le_trdeg`: coordinates in `s ≤ trdeg_{F_p} K` variables;
* `exists_polynomialCoordinates_le_one`: at most one variable when `trdeg_{F_p} K ≤ 1`.

The second covers every field of characteristic `p` that is algebraic over `F_p(t)`: finite
fields, `F_q(t)`, global function fields, and their algebraic closures.  In one variable the
elementary-group and Suslin inputs of the characteristic-`p` chain are theorems (Nagao, and the
Euclidean algorithm), which `OneVariableHost.lean` uses.

The field `K` carries an arbitrary `F_p`-algebra structure; there is only one, and it forces
`char K = p`.
-/

namespace GroupApproximation.BooneHigmanLinear.CharP

open GroupApproximation.BooneHigman.Coordinates
open GroupApproximation.BooneHigman.Metabelian.CharPCoords

/-- **Coordinates in at most `trdeg K` variables.**  A finitely generated subgroup of `GL_n(K)`,
for a field `K` over `F_p`, embeds in `GL_M(F_p[x_0, ..., x_{s-1}])` with
`s ≤ trdeg_{F_p} K`. -/
theorem exists_polynomialCoordinates_le_trdeg (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    [Algebra (ZMod p) K] (n : ℕ) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (hH : H.FG) :
    ∃ s M : ℕ, (s : Cardinal) ≤ Algebra.trdeg (ZMod p) K ∧
      ∃ ψ : H →* Matrix.GeneralLinearGroup (Fin M) (MvPolynomial (Fin s) (ZMod p)),
        Function.Injective ψ := by
  haveI : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨t, ht⟩ := exists_finset_factor H.subtype
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra (ZMod p) K, A = Algebra.adjoin (ZMod p) (↑t : Set K) :=
    ⟨_, rfl⟩
  have hsub : (↑t : Set K) ⊆ (A.toSubring : Set K) := by
    rw [Subalgebra.coe_toSubring, hA]
    exact Algebra.subset_adjoin
  obtain ⟨ρ', hρ'⟩ := ht A.toSubring hsub
  have hρ'inj : Function.Injective ρ' := factor_injective hρ' H.subtype_injective
  haveI : Algebra.FiniteType (ZMod p) A :=
    (Subalgebra.fg_iff_finiteType A).mp (by
      rw [hA]
      exact Subalgebra.fg_adjoin_finset t)
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg (ZMod p) A
  have hs : (s : Cardinal) ≤ Algebra.trdeg (ZMod p) K := by
    calc (s : Cardinal) = Algebra.trdeg (ZMod p) (MvPolynomial (Fin s) (ZMod p)) := by
          rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin]
      _ ≤ Algebra.trdeg (ZMod p) A := trdeg_le_of_injective g hginj
      _ ≤ Algebra.trdeg (ZMod p) K := trdeg_le_of_injective A.val Subtype.val_injective
  obtain ⟨f, hf⟩ := finiteDomainAwayEmbedding (ZMod p) s A g.toRingHom hginj hgfin
  let ι : ↥A.toSubring →+* ↥A :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hι : Function.Injective ι := fun x y hxy =>
    Subtype.ext (congrArg Subtype.val hxy)
  have hemb : MatrixEmbedding ↥A.toSubring (MvPolynomial (Fin s) (ZMod p)) :=
    (MatrixEmbedding.of_injective ι hι).trans
      (hf.trans (matrixEmbedding_localizationAway f))
  obtain ⟨M, ψ, hψ⟩ := hemb.exists_injective_gl n
  exact ⟨s, M, hs, ψ.comp ρ', hψ.comp hρ'inj⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.CharP.exists_polynomialCoordinates_le_trdeg

/-- **At most one variable** when `trdeg_{F_p} K ≤ 1`. -/
theorem exists_polynomialCoordinates_le_one (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    [Algebra (ZMod p) K] (htr : Algebra.trdeg (ZMod p) K ≤ 1) (n : ℕ)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) (hH : H.FG) :
    ∃ s M : ℕ, s ≤ 1 ∧
      ∃ ψ : H →* Matrix.GeneralLinearGroup (Fin M) (MvPolynomial (Fin s) (ZMod p)),
        Function.Injective ψ := by
  obtain ⟨s, M, hs, ψ, hψ⟩ := exists_polynomialCoordinates_le_trdeg p K n H hH
  exact ⟨s, M, by exact_mod_cast hs.trans htr, ψ, hψ⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.CharP.exists_polynomialCoordinates_le_one

end GroupApproximation.BooneHigmanLinear.CharP
