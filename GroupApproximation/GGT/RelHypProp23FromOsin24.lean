import GroupApproximation.GGT.RelHypFournierFacioProp23
import GroupApproximation.GGT.RelHypOsinTheorem24Verbatim
import GroupApproximation.GGT.RelHypFournierFacioGeometricBoundary
import GroupApproximation.GGT.RelHypFreeProductConedFourPoint
import GroupApproximation.GGT.RelHypSuitabilityResidue
import GroupApproximation.Algebra.HyperbolicFinitePresentation

/-!
# Fournier-Facio's Proposition 2.3 from Osin's Theorem 2.4

`GGT/RelHypFournierFacioProp23.lean` states `FournierFacioProposition23`, the
single input the manuscript's quotient sentence cites, and derives
`FournierFacioQuotientStatement` from it.  `GGT/RelHypOsinTheorem24Verbatim.lean`
states Osin's Theorem 2.4 at the statement Osin states, together with the
finite-presentation addendum that [FF25] reads off his *proof*.  This module
joins them:

    FournierFacioProposition23
      ⟸ OsinTheorem24FinitePresentationAddendum   (a published statement, plus
                                                   one clause from a published
                                                   proof)
      + HyperbolicSuitabilityStatement            (the residue)

That is the refinement in the type: one fuzzy citation becomes three sharp ones,
and the third is the only thing standing between this development and the
primary source.

## What the residue is, and why it is stated where it is

Osin's Theorem 2.4 needs `H` **suitable** in `G` (his Definition 2.2).  At the
Fournier-Facio pair the ambient group is `U ∗ H₀`, the peripheral family is
`{U}`, and the subgroup is the image of `H₀`, so the residue is a statement
about that one configuration and nothing else.

The free-product half is a theorem.
`GGT/RelHypFreeProductElementaryClosure.exists_factor_of_mem_osinElementaryClosure`
proves that the elementary closure of a factor element stays inside that factor,
so the ambient free product contributes nothing; `GGT/RelHypSuitabilityResidue`
carries that through to `isSuitableSubgroup_freeProduct_of_partner`, which
supplies suitability in `U ∗ H` for *every* `U` at once out of suitability
inside `H`.  So the hypothesis this module takes is the smaller
`HyperbolicSuitabilityStatement` -- two non-commensurable elements of infinite
order in a bare non-elementary hyperbolic group whose elementary closures meet
trivially.  That is Osin's Theorem 2.1 together with his Lemma 2.3, both §8
results, and is why it is a named input rather than a proof.

`FreeProductSuitabilityStatement` survives below as the shape the residue was
first stated in, with `freeProductSuitabilityStatement_of_hyperbolicSuitability`
recording that the smaller input implies it.

## The four clauses, and where each comes from

* **surjectivity** and the clause `π(gᵢ) ∈ π(Λ)` are Theorem 2.4's, verbatim;
* **`U ↪ Q`** is Theorem 2.4(3), injectivity on `⋃ H_λ`, read at the single
  peripheral factor;
* **torsion-freeness** is Theorem 2.4(5) against torsion-freeness of `U ∗ H₀`,
  which is `isPowerTorsionFree_coprodI` on the two factors;
* **finite presentation** is the addendum's kernel clause against
  `Group.IsFinitelyPresented.of_surjective`; it is the one clause with no
  published *statement* behind it, and keeping it visible is the point of the
  split.

The relative hyperbolicity hypothesis of Theorem 2.4 is discharged outright, by
`freeProductRelativelyHyperbolicStatement_proved` -- Osin's Memoirs Theorem 2.34
for free products, which this development proves.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid

/-! ## 1.  The residue -/

/-- **Suitability of `H₀` in `U ∗ H₀`**, in Osin's sense (Definition 2.2), at the
one configuration the Fournier-Facio paragraph uses.

The peripheral family is the single factor `U` and the subgroup is the image of
the partner factor, which is `MonoidHom.range (freeProductPartnerHom U H)`;
`freeProductPeripheral U H` is `MonoidHom.range (freeProductSourceHom U H)` on
the nose.

`IsPowerTorsionFree U` is deliberately **not** a hypothesis: hyperbolicity of the
witnesses in `U ∗ H₀` is free-product normal form and says nothing about `U`, and
their infinite order is torsion-freeness of `H₀` alone.  That omission is
vindicated by the proof `GGT/RelHypSuitabilityResidue.lean` gives of the
reduction below, in which `U` does not appear at all. -/
def FreeProductSuitabilityStatement : Prop :=
  ∀ (U H : Type) (_ : Group U) (_ : Group H),
    IsNonElementaryHyperbolic H → IsPowerTorsionFree H →
      IsSuitableSubgroup (fun _ : Unit => freeProductPeripheral U H)
        (MonoidHom.range (freeProductPartnerHom U H))

/-- **The free-product statement follows from the residue at one group.**

`GGT/RelHypSuitabilityResidue.HyperbolicSuitabilityStatement` asks only for
suitability of `⊤` in a bare non-elementary hyperbolic group, with an empty
peripheral family; the passage to `U ∗ H` for every `U` at once is a theorem
there.  So the residue this development actually owes is the smaller statement,
and `FreeProductSuitabilityStatement` is kept only because it is the shape the
bridge below was first written against and the shape that module's docstring
names. -/
theorem freeProductSuitabilityStatement_of_hyperbolicSuitability
    (h : HyperbolicSuitabilityStatement) : FreeProductSuitabilityStatement :=
  fun U H _ _ hne htf =>
    isSuitableSubgroup_freeProduct_of_hyperbolicSuitability h U H hne htf

/-! ## 2.  The bridge -/

/-- **Fournier-Facio's Proposition 2.3 from Osin's Theorem 2.4 and the
suitability residue.** -/
theorem fournierFacioProposition23_of_osin24
    (hOsin : OsinTheorem24FinitePresentationAddendum)
    (hSuit : HyperbolicSuitabilityStatement) :
    FournierFacioProposition23 := by
  intro K Lam instK instLam hne htfLam hfpK htfK g hgfin
  haveI := hfpK
  haveI : Group.IsFinitelyPresented Lam :=
    @Hyperbolic.isFinitelyPresented_of_isHyperbolicGroup Lam instLam hne.1
  have hrh : IsRelativelyHyperbolic (CoprodI (pairFamily K Lam))
      (fun _ : Unit => freeProductPeripheral K Lam) :=
    freeProductRelativelyHyperbolicStatement_proved K Lam instK instLam hne.1
  have hsuit : IsSuitableSubgroup (fun _ : Unit => freeProductPeripheral K Lam)
      (MonoidHom.range (freeProductPartnerHom K Lam)) :=
    @isSuitableSubgroup_freeProduct_of_hyperbolicSuitability hSuit K Lam instK
      instLam hne htfLam
  obtain ⟨Q, instQ, eta, hquot, hker⟩ :=
    hOsin (CoprodI (pairFamily K Lam)) inferInstance Unit
      (fun _ : Unit => freeProductPeripheral K Lam) hrh
      (MonoidHom.range (freeProductPartnerHom K Lam)) hsuit g hgfin
  have hsourceTf : IsPowerTorsionFree (CoprodI (pairFamily K Lam)) :=
    OsinWeightedMetric.isPowerTorsionFree_coprodI
      (isPowerTorsionFree_pairFamily htfK htfLam)
  have hQtf : IsPowerTorsionFree Q := hquot.isPowerTorsionFree hsourceTf
  obtain ⟨hsurj, -, hmem, hinjOn, -, -⟩ := hquot
  refine ⟨Q, instQ, eta, hsurj, ?_, ?_, ?_, ?_⟩
  · exact Group.IsFinitelyPresented.of_surjective eta hsurj hker
  · exact hQtf
  · intro a b hab
    have hmemA : (freeProductSourceHom K Lam a : CoprodI (pairFamily K Lam))
        ∈ ⋃ _ : Unit,
          ((freeProductPeripheral K Lam :
            Subgroup (CoprodI (pairFamily K Lam))) :
              Set (CoprodI (pairFamily K Lam))) :=
      Set.mem_iUnion.mpr ⟨(), ⟨a, rfl⟩⟩
    have hmemB : (freeProductSourceHom K Lam b : CoprodI (pairFamily K Lam))
        ∈ ⋃ _ : Unit,
          ((freeProductPeripheral K Lam :
            Subgroup (CoprodI (pairFamily K Lam))) :
              Set (CoprodI (pairFamily K Lam))) :=
      Set.mem_iUnion.mpr ⟨(), ⟨b, rfl⟩⟩
    exact CoprodI.of_injective false (hinjOn hmemA hmemB hab)
  · intro x hx
    have h := hmem x hx
    rwa [← MonoidHom.range_comp] at h

end RelHyp
end GGT
end GroupApproximation
