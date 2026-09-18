import GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighWittEBase
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.GroupTheory.Finiteness
import GroupApproximation.Meta.AxiomGuard

/-!
# Noether normalization lift for `ZMod (p ^ e)[Q]` (bh-met-87h, part 3)

This is `PureCharPrimeEHighWittModRedNorm.lean` with `p²` replaced by `p ^ e`.  Let
`R = ZMod (p ^ e)[Q]` with `Q` a finitely generated commutative group, and let `P` be a prime of
`R` with `p ∈ P`.  Then `R/P` is a finitely generated `𝔽_p`-domain, and Noether normalization
(`exists_finite_inj_algHom_of_fg`) gives an injective finite `g : 𝔽_p[X₁..X_d] → R/P`.  Lifting
the images of the variables to `t : Fin d → R` gives `ψ : ZMod (p ^ e)[X₁..X_d] → R` with
`mk_P ∘ ψ = g ∘ red`.  Hence `ψ S ∩ P = ∅` and `mk_P ∘ ψ` is finite.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

/-- **Noether normalization lift.**  A ring map `ψ : ZMod (p ^ e)[X₁..X_d] → ZMod (p ^ e)[Q]`
sends `S` outside `P` and makes `ZMod (p ^ e)[Q]/P` finite over `ZMod (p ^ e)[X₁..X_d]`. -/
theorem eHighWittE_normalization (p e : ℕ) [NeZero e] [Fact p.Prime] (Q : Type) [CommGroup Q]
    [Group.FG Q] (P : Ideal (MonoidAlgebra (ZMod (p ^ e)) Q)) [P.IsPrime]
    (hpP : ((p : ℕ) : MonoidAlgebra (ZMod (p ^ e)) Q) ∈ P) :
    ∃ (d : ℕ) (ψ : MvPolynomial (Fin d) (ZMod (p ^ e)) →+* MonoidAlgebra (ZMod (p ^ e)) Q),
      (∀ a ∈ eHighWittE_S p e (Fin d), ψ a ∉ P) ∧ ((Ideal.Quotient.mk P).comp ψ).Finite := by
  have hp : p.Prime := Fact.out
  haveI : CharP (MonoidAlgebra (ZMod (p ^ e)) Q ⧸ P) p := by
    refine (CharP.charP_iff_prime_eq_zero hp).mpr ?_
    rw [← map_natCast (Ideal.Quotient.mk P) p, Ideal.Quotient.eq_zero_iff_mem]
    exact hpP
  letI : Algebra (ZMod p) (MonoidAlgebra (ZMod (p ^ e)) Q ⧸ P) :=
    ZMod.algebra (MonoidAlgebra (ZMod (p ^ e)) Q ⧸ P) p
  letI : Algebra (ZMod (p ^ e)) (ZMod p) :=
    ZMod.algebra' (ZMod p) p (dvd_pow_self p (NeZero.ne e))
  haveI : IsScalarTower (ZMod (p ^ e)) (ZMod p) (MonoidAlgebra (ZMod (p ^ e)) Q ⧸ P) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.FiniteType (ZMod p) (MonoidAlgebra (ZMod (p ^ e)) Q ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (ZMod (p ^ e)) (ZMod p)
      (MonoidAlgebra (ZMod (p ^ e)) Q ⧸ P)
  obtain ⟨d, g, hg, hgf⟩ := exists_finite_inj_algHom_of_fg (ZMod p)
    (MonoidAlgebra (ZMod (p ^ e)) Q ⧸ P)
  choose t ht using fun i : Fin d => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  have key : (Ideal.Quotient.mk P).comp
      (MvPolynomial.eval₂Hom (algebraMap (ZMod (p ^ e)) (MonoidAlgebra (ZMod (p ^ e)) Q)) t) =
      g.toRingHom.comp (eHighWittE_red p e (Fin d)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · exact RingHom.congr_fun (RingHom.ext_zmod
        (((Ideal.Quotient.mk P).comp (MvPolynomial.eval₂Hom
          (algebraMap (ZMod (p ^ e)) (MonoidAlgebra (ZMod (p ^ e)) Q)) t)).comp MvPolynomial.C)
        ((g.toRingHom.comp (eHighWittE_red p e (Fin d))).comp MvPolynomial.C)) r
    · show Ideal.Quotient.mk P (MvPolynomial.eval₂Hom
          (algebraMap (ZMod (p ^ e)) (MonoidAlgebra (ZMod (p ^ e)) Q)) t (MvPolynomial.X i)) =
        g (eHighWittE_red p e (Fin d) (MvPolynomial.X i))
      rw [MvPolynomial.eval₂Hom_X', eHighWittE_red, MvPolynomial.map_X]
      exact ht i
  have hsurj : Function.Surjective (eHighWittE_red p e (Fin d)) := by
    rw [eHighWittE_red]
    exact MvPolynomial.map_surjective _ (ZMod.castHom_surjective _)
  have hgf' : g.toRingHom.Finite := hgf
  refine ⟨d, MvPolynomial.eval₂Hom (algebraMap (ZMod (p ^ e))
    (MonoidAlgebra (ZMod (p ^ e)) Q)) t, fun a ha h => ?_, ?_⟩
  · have h1 : Ideal.Quotient.mk P (MvPolynomial.eval₂Hom (algebraMap (ZMod (p ^ e))
        (MonoidAlgebra (ZMod (p ^ e)) Q)) t a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    have h2 : g (eHighWittE_red p e (Fin d) a) = 0 := (RingHom.congr_fun key a).symm.trans h1
    have h3 : eHighWittE_red p e (Fin d) a = 0 := hg (h2.trans (map_zero g).symm)
    have ha' : eHighWittE_red p e (Fin d) a ∈ nonZeroDivisors (MvPolynomial (Fin d) (ZMod p)) :=
      Submonoid.mem_comap.mp ha
    rw [h3] at ha'
    exact zero_notMem_nonZeroDivisors ha'
  · rw [key]
    exact hgf'.comp (RingHom.Finite.of_surjective _ hsurj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighWittE_normalization

end GroupApproximation.BooneHigman.Metabelian.Coprimary
