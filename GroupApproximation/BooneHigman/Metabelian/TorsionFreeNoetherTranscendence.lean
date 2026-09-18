import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import GroupApproximation.Meta.AxiomGuard

/-!
# Torsion-free linearity, coprimary case: a transcendence lift (lane bh-met-43)

Let `P` be an ideal of a commutative ring `A` that contains no nonzero integer.  Then `ℤ → A ⧸ P`
is injective, so `A ⧸ P` has a transcendence basis `s` over `ℤ` (`exists_isTranscendenceBasis`).
Lifting `s` to `A` gives a ring map `g : ℤ[s] → A` with

* `g d ∉ P` for every nonzero polynomial `d` (algebraic independence of `s` in `A ⧸ P`);
* every `a : A` is a root modulo `P` of a nonzero polynomial over `ℤ[s]` (the quotient `A ⧸ P`
  is algebraic over `ℤ[s] ≅ ℤ[range s]`).

This replaces Noether normalization in the generic-localization argument: inverting the
nonzero elements of `ℤ[s]` makes `A ⧸ P` algebraic over a field of characteristic zero.

* `noether_exists_transcendence_lift`: the endpoint.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- **Transcendence lift.** For an ideal `P` of a commutative ring containing no nonzero integer,
there are polynomial variables `ι` and a ring map `g : ℤ[ι] → A` such that nonzero polynomials
map outside `P`, and every element of `A` is a root modulo `P` of a nonzero polynomial with
coefficients in `ℤ[ι]`. -/
theorem noether_exists_transcendence_lift {A : Type} [CommRing A] (P : Ideal A)
    (hP : ∀ n : ℤ, n ≠ 0 → (n : A) ∉ P) :
    ∃ (ι : Type) (g : MvPolynomial ι ℤ →+* A),
      (∀ d : MvPolynomial ι ℤ, d ≠ 0 → g d ∉ P) ∧
      ∀ a : A, ∃ p : Polynomial (MvPolynomial ι ℤ), p ≠ 0 ∧ p.eval₂ g a ∈ P := by
  have hinjZ : Function.Injective (algebraMap ℤ (A ⧸ P)) := by
    refine (injective_iff_map_eq_zero (algebraMap ℤ (A ⧸ P))).2 fun n hn => ?_
    by_contra h0
    apply hP n h0
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast, ← eq_intCast (algebraMap ℤ (A ⧸ P)) n]
    exact hn
  haveI : FaithfulSMul ℤ (A ⧸ P) := (faithfulSMul_iff_algebraMap_injective ℤ (A ⧸ P)).2 hinjZ
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ (A ⧸ P)
  choose xt hxt using fun i : s => Ideal.Quotient.mk_surjective (i : A ⧸ P)
  obtain ⟨g, hg⟩ : ∃ g : MvPolynomial s ℤ →+* A, ∀ d : MvPolynomial s ℤ,
      Ideal.Quotient.mk P (g d) = MvPolynomial.aeval ((↑) : s → A ⧸ P) d := by
    refine ⟨MvPolynomial.eval₂Hom (Int.castRingHom A) xt, fun d => ?_⟩
    rw [MvPolynomial.aeval_def, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left,
      RingHom.ext_int ((Ideal.Quotient.mk P).comp (Int.castRingHom A)) (algebraMap ℤ (A ⧸ P)),
      show (⇑(Ideal.Quotient.mk P) ∘ xt) = ((↑) : s → A ⧸ P) from funext hxt]
  have hinj := algebraicIndependent_iff_injective_aeval.1 hs.1
  refine ⟨s, g, fun d hd hmem => hd (hinj (((hg d).symm.trans
    (Ideal.Quotient.eq_zero_iff_mem.2 hmem)).trans
      (map_zero (MvPolynomial.aeval ((↑) : s → A ⧸ P))).symm)), fun a => ?_⟩
  haveI := hs.isAlgebraic
  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic
    (R := Algebra.adjoin ℤ (Set.range ((↑) : s → A ⧸ P))) (Ideal.Quotient.mk P a)
  obtain ⟨F, hF, hFe⟩ : ∃ F : Algebra.adjoin ℤ (Set.range ((↑) : s → A ⧸ P)) →+*
      MvPolynomial s ℤ, Function.Injective F ∧ ∀ y, hs.1.aevalEquiv (F y) = y :=
    ⟨hs.1.aevalEquiv.symm.toRingEquiv.toRingHom, hs.1.aevalEquiv.symm.injective,
      hs.1.aevalEquiv.apply_symm_apply⟩
  have hcomp : ((Ideal.Quotient.mk P).comp g).comp F =
      algebraMap (Algebra.adjoin ℤ (Set.range ((↑) : s → A ⧸ P))) (A ⧸ P) := by
    refine RingHom.ext fun y => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, hg, ← hs.1.algebraMap_aevalEquiv, hFe]
  refine ⟨p.map F, (Polynomial.map_ne_zero_iff hF).2 hp0, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp,
    ← Polynomial.aeval_def]
  exact hpx

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.noether_exists_transcendence_lift

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
