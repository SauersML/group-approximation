import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import GroupApproximation.BooneHigman.Coordinates.MatrixEmbedding
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsNagata
import GroupApproximation.Meta.AxiomGuard

/-!
# Inverting one polynomial keeps polynomial matrix coordinates (lane bh-met-03)

Research node `char-p-polynomial-embedding-via-noether-normalization`, step "generic
freeness ... then `A_f` is free over `P_f`, so `A_f` embeds in a matrix ring over `P_f`".
That route still has to get rid of the denominator `f`; the node appeals to miracle
flatness and Quillen--Suslin.  This file replaces that step by an elementary argument:

  for every `f ∈ P = k[x_1, ..., x_s]`, the localization `P[1/f]` embeds in a matrix ring
  over `P` itself.

**Route.**  `P[1/f] ≅ P[X]/(f X - 1)` (`Localization.awayEquivAdjoin`).  For any nonzero
`g ∈ P[X] = k[x_0, ..., x_s]`, Nagata's change of variables
(`Nagata.exists_algEquiv_isUnit_leadingCoeff`) gives a ring automorphism `Φ` of `P[X]` such
that `Φ g` has a unit leading coefficient in `X`; hence
`P[X]/(g) ≅ P[X]/(Φ g) = P[X]/(u⁻¹ Φ g)` with `u⁻¹ Φ g` monic, and `P[X]/(monic)` is free of
finite rank over `P` (`AdjoinRoot.powerBasis'`), so it embeds by left multiplication matrices
(`MatrixEmbedding.of_basis`).  No hypothesis `f ≠ 0` is needed: `f X - 1 ≠ 0` always.

Main declarations: `quotSpanEquivAdjoinRoot`, `matrixEmbedding_adjoinRoot`,
`matrixEmbedding_localizationAway`.
-/

open Polynomial
open GroupApproximation.BooneHigman.Coordinates

namespace GroupApproximation.BooneHigman.Metabelian.CharPCoords

/-- The quotient `R[X] ⧸ (q)` is ring-isomorphic to `AdjoinRoot q` (the kernel of
`AdjoinRoot.mk q` is `(q)`). -/
noncomputable def quotSpanEquivAdjoinRoot {R : Type*} [CommRing R] (q : R[X]) :
    R[X] ⧸ Ideal.span {q} ≃+* AdjoinRoot q :=
  (Ideal.quotEquivOfEq (show Ideal.span {q} = RingHom.ker (AdjoinRoot.mk q) from
    Ideal.ext fun x => by
      rw [RingHom.mem_ker, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton])).trans
    (RingHom.quotientKerEquivOfSurjective (AdjoinRoot.mk_surjective q))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.quotSpanEquivAdjoinRoot

/-- For a nonzero `g ∈ P[X]`, `P = k[x_0, ..., x_{s-1}]`, the ring `P[X]/(g)` embeds in a
matrix ring over `P`. -/
theorem matrixEmbedding_adjoinRoot {k : Type*} [Field k] {s : ℕ}
    (g : (MvPolynomial (Fin s) k)[X]) (hg : g ≠ 0) :
    MatrixEmbedding (AdjoinRoot g) (MvPolynomial (Fin s) k) := by
  have hF : (MvPolynomial.finSuccEquiv k s).symm g ≠ 0 := by
    intro h
    apply hg
    exact (MvPolynomial.finSuccEquiv k s).symm.injective (by rw [h, map_zero])
  obtain ⟨e, he⟩ := Nagata.exists_algEquiv_isUnit_leadingCoeff _ hF
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (MvPolynomial (Fin s) k)[X] ≃+* (MvPolynomial (Fin s) k)[X],
      Φ g = MvPolynomial.finSuccEquiv k s (e ((MvPolynomial.finSuccEquiv k s).symm g)) :=
    ⟨((MvPolynomial.finSuccEquiv k s).symm.trans
      (e.trans (MvPolynomial.finSuccEquiv k s))).toRingEquiv, rfl⟩
  have hu : IsUnit (Φ g).leadingCoeff := by
    rw [hΦ]
    exact he
  have hmonic : (hu.unit⁻¹ • Φ g).Monic := Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hu
  have hJ : Ideal.span {Φ g} =
      (Ideal.span {g}).map (Φ : (MvPolynomial (Fin s) k)[X] →+* (MvPolynomial (Fin s) k)[X]) :=
    ((Ideal.map_span (Φ : (MvPolynomial (Fin s) k)[X] →+* (MvPolynomial (Fin s) k)[X])
      {g}).trans (congrArg Ideal.span Set.image_singleton)).symm
  have hJ' : Ideal.span {Φ g} = Ideal.span {hu.unit⁻¹ • Φ g} := by
    rw [Units.smul_def, Polynomial.smul_eq_C_mul,
      Ideal.span_singleton_mul_left_unit ((hu.unit⁻¹).isUnit.map Polynomial.C)]
  let ψ : AdjoinRoot g ≃+* AdjoinRoot (hu.unit⁻¹ • Φ g) :=
    (quotSpanEquivAdjoinRoot g).symm.trans ((Ideal.quotientEquiv _ _ Φ hJ).trans
      ((Ideal.quotEquivOfEq hJ').trans (quotSpanEquivAdjoinRoot (hu.unit⁻¹ • Φ g))))
  exact (MatrixEmbedding.of_injective ψ.toRingHom ψ.injective).trans
    (MatrixEmbedding.of_basis (AdjoinRoot.powerBasis' hmonic).basis)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.matrixEmbedding_adjoinRoot

/-- **Denominators are free.**  For every `f ∈ P = k[x_0, ..., x_{s-1}]` the localization
`P[1/f]` embeds in a matrix ring over `P`. -/
theorem matrixEmbedding_localizationAway {k : Type*} [Field k] {s : ℕ}
    (f : MvPolynomial (Fin s) k) :
    MatrixEmbedding (Localization.Away f) (MvPolynomial (Fin s) k) := by
  have hg : (Polynomial.C f * Polynomial.X - 1 : (MvPolynomial (Fin s) k)[X]) ≠ 0 := by
    intro h0
    have h1 := congrArg (Polynomial.eval (0 : MvPolynomial (Fin s) k)) h0
    simp at h1
  exact (MatrixEmbedding.of_injective (Localization.awayEquivAdjoin f).toRingEquiv.toRingHom
    (Localization.awayEquivAdjoin f).injective).trans (matrixEmbedding_adjoinRoot _ hg)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharPCoords.matrixEmbedding_localizationAway

end GroupApproximation.BooneHigman.Metabelian.CharPCoords
