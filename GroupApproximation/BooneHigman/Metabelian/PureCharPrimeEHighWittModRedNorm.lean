import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittCoeffLoc
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.GroupTheory.Finiteness
import GroupApproximation.Meta.AxiomGuard

/-!
# Noether normalization lift (bh-met-87g, part 1)

Let `R = ZMod (p²)[Q]`, where `Q` is a finitely generated commutative group, and let `P` be a
prime of `R` with `p ∈ P`. Then `R/P` is a finitely generated `𝔽_p`-domain. Mathlib's Noether
normalization (`exists_finite_inj_algHom_of_fg`) gives an injective finite
`g : 𝔽_p[X₁..X_d] → R/P`. Lift the images of the variables to `t : Fin d → R`, and let
`ψ : D₀ = ZMod (p²)[X₁..X_d] → R` be the evaluation map at `t`. Then:
* `mk_P ∘ ψ = g ∘ red`;
* if `a ∈ S` (that is, `red a` is a nonzerodivisor, hence nonzero), then `ψ a ∉ P`, because
  `g` is injective;
* `mk_P ∘ ψ` is finite, being a finite map composed with a surjection.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Noether normalization lift.** There is a ring map `ψ : ZMod (p²)[X₁..X_d] → ZMod (p²)[Q]`
that sends `S` outside `P` and makes `ZMod (p²)[Q]/P` finite over `ZMod (p²)[X₁..X_d]`. -/
theorem eHighWittModRed_normalization (p : ℕ) [Fact p.Prime] (Q : Type) [CommGroup Q]
    [Group.FG Q] (P : Ideal (MonoidAlgebra (ZMod (p ^ 2)) Q)) [P.IsPrime]
    (hpP : ((p : ℕ) : MonoidAlgebra (ZMod (p ^ 2)) Q) ∈ P) :
    ∃ (d : ℕ) (ψ : MvPolynomial (Fin d) (ZMod (p ^ 2)) →+* MonoidAlgebra (ZMod (p ^ 2)) Q),
      (∀ a ∈ eHighWittCoeff_S p (Fin d), ψ a ∉ P) ∧ ((Ideal.Quotient.mk P).comp ψ).Finite := by
  have hp : p.Prime := Fact.out
  haveI : CharP (MonoidAlgebra (ZMod (p ^ 2)) Q ⧸ P) p := by
    refine (CharP.charP_iff_prime_eq_zero hp).mpr ?_
    rw [← map_natCast (Ideal.Quotient.mk P) p, Ideal.Quotient.eq_zero_iff_mem]
    exact hpP
  letI : Algebra (ZMod p) (MonoidAlgebra (ZMod (p ^ 2)) Q ⧸ P) :=
    ZMod.algebra (MonoidAlgebra (ZMod (p ^ 2)) Q ⧸ P) p
  letI : Algebra (ZMod (p ^ 2)) (ZMod p) :=
    ZMod.algebra' (ZMod p) p (dvd_pow_self p (two_ne_zero : (2 : ℕ) ≠ 0))
  haveI : IsScalarTower (ZMod (p ^ 2)) (ZMod p) (MonoidAlgebra (ZMod (p ^ 2)) Q ⧸ P) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.FiniteType (ZMod p) (MonoidAlgebra (ZMod (p ^ 2)) Q ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (ZMod (p ^ 2)) (ZMod p)
      (MonoidAlgebra (ZMod (p ^ 2)) Q ⧸ P)
  obtain ⟨d, g, hg, hgf⟩ := exists_finite_inj_algHom_of_fg (ZMod p)
    (MonoidAlgebra (ZMod (p ^ 2)) Q ⧸ P)
  choose t ht using fun i : Fin d => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  have key : (Ideal.Quotient.mk P).comp
      (MvPolynomial.eval₂Hom (algebraMap (ZMod (p ^ 2)) (MonoidAlgebra (ZMod (p ^ 2)) Q)) t) =
      g.toRingHom.comp (eHighWittCoeff_red p (Fin d)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · exact RingHom.congr_fun (RingHom.ext_zmod
        (((Ideal.Quotient.mk P).comp (MvPolynomial.eval₂Hom
          (algebraMap (ZMod (p ^ 2)) (MonoidAlgebra (ZMod (p ^ 2)) Q)) t)).comp MvPolynomial.C)
        ((g.toRingHom.comp (eHighWittCoeff_red p (Fin d))).comp MvPolynomial.C)) r
    · show Ideal.Quotient.mk P (MvPolynomial.eval₂Hom
          (algebraMap (ZMod (p ^ 2)) (MonoidAlgebra (ZMod (p ^ 2)) Q)) t (MvPolynomial.X i)) =
        g (eHighWittCoeff_red p (Fin d) (MvPolynomial.X i))
      rw [MvPolynomial.eval₂Hom_X', eHighWittCoeff_red, MvPolynomial.map_X]
      exact ht i
  have hsurj : Function.Surjective (eHighWittCoeff_red p (Fin d)) := by
    rw [eHighWittCoeff_red]
    exact MvPolynomial.map_surjective _ (ZMod.castHom_surjective _)
  have hgf' : g.toRingHom.Finite := hgf
  refine ⟨d, MvPolynomial.eval₂Hom (algebraMap (ZMod (p ^ 2))
    (MonoidAlgebra (ZMod (p ^ 2)) Q)) t, fun a ha h => ?_, ?_⟩
  · have h1 : Ideal.Quotient.mk P (MvPolynomial.eval₂Hom (algebraMap (ZMod (p ^ 2))
        (MonoidAlgebra (ZMod (p ^ 2)) Q)) t a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    have h2 : g (eHighWittCoeff_red p (Fin d) a) = 0 := (RingHom.congr_fun key a).symm.trans h1
    have h3 : eHighWittCoeff_red p (Fin d) a = 0 := hg (h2.trans (map_zero g).symm)
    have ha' : eHighWittCoeff_red p (Fin d) a ∈ nonZeroDivisors (MvPolynomial (Fin d) (ZMod p)) :=
      ha
    rw [h3] at ha'
    exact zero_notMem_nonZeroDivisors ha'
  · rw [key]
    exact hgf'.comp (RingHom.Finite.of_surjective _ hsurj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittModRed_normalization

end GroupApproximation.BooneHigman.Metabelian.Coprimary
