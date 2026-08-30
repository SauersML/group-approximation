import GroupApproximation.GGT.RelHypFreeProductPartnerFills
import GroupApproximation.GGT.RelHypKazhdanNonElementary
import GroupApproximation.Algebra.ProductFinitePresentation

/-!
# The Fournier-Facio quotient sentence, at the statement its source actually
states

`Manuscript/NonMF/FournierFacioInput.lean`'s third literature field,
`smallCancellationQuotient : FournierFacioQuotientStatement`, has been carried
through four generations of a transcription of **Osin's §4 small-cancellation
machinery**, each refuted:
`GGT/RelHypOsinTheorem24Refuted.lean`, `GGT/RelHypOsin24Collapse.lean` (which
refutes the second and third generations), and the fourth,
`GGT/RelHypOsin24CayleyLeaf.lean`, which is unfaithful in four places recorded
in issue #52.

The machinery was never the citation.  Reading the sources:

* **Osin**, *Small cancellations over relatively hyperbolic groups and embedding
  theorems*, Ann. of Math. **172** (2010) 1--39 (arXiv:math/0411039),
  **Theorem 2.4** has no small-cancellation hypothesis at all.  It reads: `G`
  hyperbolic relative to `{H_λ}`, `H` a *suitable* subgroup, `t₁,…,t_m ∈ G`;
  then there is an epimorphism `η : G → Ḡ` with (1) `Ḡ` hyperbolic relative to
  `{η(H_λ)}`, (2) `η(tᵢ) ∈ η(H)`, (3) `η` injective on `⋃ H_λ`, (4) `η(H)`
  suitable, (5) every finite-order element of `Ḡ` is the image of one of `G`.
  The condition `C(ε, µ, λ, c, ρ)` is Definition 4.2, machinery used in §4--§8
  to *prove* Theorem 2.4.
* **Fournier-Facio**, *A torsion-free non-sofic group* (arXiv:2608.02025) --
  the manuscript's `[FFF]` -- cites, for this very sentence, `[FF25,
  Proposition 2.3]` for the quotient and `[Osi10, Theorem 2.4(5)]` for
  torsion-freeness.  It cites no relator design, because none is owed: the
  relators live inside the proof of a theorem being cited.
* **Fournier-Facio**, *Stability, approximable quotients, and higher property
  (T)* (arXiv:2512.09180) = `[FF25]`, **Proposition 2.3**: "Let `Λ` be a
  non-elementary hyperbolic group with no non-trivial finite normal subgroups,
  and let `K` be a (finitely presented) group.  Let `g₁,…,g_k ∈ Γ := Λ ∗ K`.
  Then there exists a (finitely presented) quotient `π : Γ → Γ̄` that is
  injective on `K`, such that `Γ̄` is hyperbolic relative to `π(K)`, has no
  non-trivial finite normal subgroups, and such that `π(gᵢ) ∈ π(Λ)`."

`FournierFacioProposition23` below is that statement, and the whole literature
debt of the quotient sentence.  `OsinRelatorDesign` and its three successors are
retired: they were artifacts of transcribing the machinery, not statements
anybody has made.

## What is transcribed, and what is deliberately dropped

Hypotheses, in order: `Λ` non-elementary hyperbolic; `Λ` torsion-free; `K`
finitely presented; `K` torsion-free.

* **"no non-trivial finite normal subgroups"** is discharged by torsion-freeness
  of `Λ`, which is stronger and is what the manuscript has.
* **`Λ` finitely presented is NOT a hypothesis**, and the history is worth
  keeping.  Proposition 2.3 does not state it either -- there it is implied by
  `Λ` hyperbolic -- but this `Prop` carried it for a while, because
  `Hyperbolic.IsHyperbolicGroup` is a finite generating set satisfying the
  four-point condition, which gives finite *generation*, and "hyperbolic implies
  finitely presented" was a theorem this repository did not have.  The model
  test below is what found that, at the trivial source, where the
  finite-presentation clause of the conclusion is otherwise underivable.  The
  repository now proves it outright --
  `Hyperbolic.isFinitelyPresented_of_isHyperbolicGroup`, with no literature
  input -- so `hne.1` supplies it and the hypothesis is gone.  Dropping it makes
  this `Prop` **stronger and more faithful at once**: strictly fewer hypotheses,
  and exactly the hypothesis list the source states.
* **`K` torsion-free** is not in Proposition 2.3 either.  It is here because the
  torsion clause folded in from `[Osi10, Theorem 2.4(5)]` converts
  torsion-freeness of `Γ = Λ ∗ K` into torsion-freeness of `Γ̄`, and `Γ` is
  torsion-free exactly when both factors are.

Two conclusion clauses of Proposition 2.3 are **dropped**: that `Γ̄` is
hyperbolic relative to `π(K)`, and that `Γ̄` has no non-trivial finite normal
subgroups.  Neither is consumed downstream.  Dropping them makes this `Prop`
strictly *weaker*, which is the safe direction for something in hypothesis
position, and adding either back later is additive.  Nothing is dropped that the
manuscript uses.

## What is proved here

`exists_quotient_of_subsingleton_source` -- the model test the standing rule
asks for, exhibiting every clause of the conclusion simultaneously satisfied at
the smallest source; and `fournierFacioQuotientStatement_of_prop23`, the
derivation of the manuscript's field, which spends `Infinite H₀` and property
`(T)` on non-elementarity of `H₀` through `isNonElementaryHyperbolic_of_kazhdan'`
exactly as every earlier generation did.  `Group.IsFinitelyPresented H₀`, which
that hypothesis list also carries, is not spent: it was load-bearing only while
this `Prop` demanded finite presentation of `Λ`, and since
`Hyperbolic.isFinitelyPresented_of_isHyperbolicGroup` landed it is derivable
from hyperbolicity and the demand is gone.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid

/-! ## 1.  The statement -/

/-- **Fournier-Facio, arXiv:2512.09180, Proposition 2.3**, with the torsion
clause of **Osin, Ann. of Math. 172 (2010), Theorem 2.4(5)** folded in.

The peripheral factor is `K` -- index `false` of `pairFamily K Lam` -- and the
hyperbolic factor is `Lam`, so `CoprodI (pairFamily K Lam)` is Proposition 2.3's
`Γ = Λ ∗ K`, `freeProductSourceHom` is the inclusion of `K`, and
`freeProductPartnerHom` is the inclusion of `Λ`.

The finitely many prescribed elements `g₁,…,g_k ∈ Γ` are a finite set of `Γ`.
The four conclusion clauses are, in order: `π` is a quotient map; `Γ̄` is
finitely presented; `Γ̄` is torsion-free (this is the Osin 2.4(5) clause); `π` is
injective on `K`; and each prescribed element lands in the image of `Λ`. -/
def FournierFacioProposition23 : Prop :=
  ∀ (K Lam : Type) (_ : Group K) (_ : Group Lam),
    IsNonElementaryHyperbolic Lam → IsPowerTorsionFree Lam →
      Group.IsFinitelyPresented K → IsPowerTorsionFree K →
        ∀ g : Set (CoprodI (pairFamily K Lam)), g.Finite →
          ∃ (Q : Type) (_ : Group Q) (pi : CoprodI (pairFamily K Lam) →* Q),
            Function.Surjective pi ∧
              Group.IsFinitelyPresented Q ∧
                IsPowerTorsionFree Q ∧
                  Function.Injective (pi.comp (freeProductSourceHom K Lam)) ∧
                    ∀ x ∈ g,
                      pi x ∈ (pi.comp (freeProductPartnerHom K Lam)).range

/-! ## 2.  The model test -/

/-- **Every clause of the conclusion is simultaneously satisfiable**, at the
smallest source: with `K` trivial, `Λ ∗ K` is its own quotient.

This is the check the standing rule asks for before a `Prop` goes into
hypothesis position, and on this statement it was not a formality: it is what
found that the finite-presentation clause of the conclusion was underivable even
here, where the quotient map is the identity, because
`Hyperbolic.IsHyperbolicGroup` gives finite generation and not finite
presentation.  That gap was closed the other way round in the end --
`Hyperbolic.isFinitelyPresented_of_isHyperbolicGroup` now proves the missing
step, so the hypothesis the test called for has been removed again rather than
kept.  The test keeps `[Group.IsFinitelyPresented Lam]` as an instance binder of
its own, since it has no hyperbolicity hypothesis to derive it from.

The last clause is `surjective_partner_of_sourceGen` at the empty generating
set: a trivial source is generated by `∅`, so its hypothesis is vacuous and the
partner fills the free product outright. -/
theorem exists_quotient_of_subsingleton_source (K Lam : Type) [Group K]
    [Group Lam] [Group.IsFinitelyPresented K] [Group.IsFinitelyPresented Lam]
    (hKtriv : ∀ x : K, x = 1) (hKtf : IsPowerTorsionFree K)
    (hLtf : IsPowerTorsionFree Lam) (g : Set (CoprodI (pairFamily K Lam))) :
    ∃ (Q : Type) (_ : Group Q) (pi : CoprodI (pairFamily K Lam) →* Q),
      Function.Surjective pi ∧
        Group.IsFinitelyPresented Q ∧
          IsPowerTorsionFree Q ∧
            Function.Injective (pi.comp (freeProductSourceHom K Lam)) ∧
              ∀ x ∈ g,
                pi x ∈ (pi.comp (freeProductPartnerHom K Lam)).range := by
  have hgen : Subgroup.closure (∅ : Set K) = ⊤ := by
    refine (Subgroup.eq_top_iff' _).mpr ?_
    intro x
    rw [hKtriv x]
    exact one_mem _
  have hmem : ∀ x ∈ (∅ : Set K),
      (MonoidHom.id (CoprodI (pairFamily K Lam))) (freeProductSourceHom K Lam x)
        ∈ ((MonoidHom.id (CoprodI (pairFamily K Lam))).comp
            (freeProductPartnerHom K Lam)).range := by
    intro x hx
    simp at hx
  have hpartner : Function.Surjective
      ((MonoidHom.id (CoprodI (pairFamily K Lam))).comp
        (freeProductPartnerHom K Lam)) :=
    surjective_partner_of_sourceGen (MonoidHom.id _) Function.surjective_id
      hgen hmem
  have htf : IsPowerTorsionFree (CoprodI (pairFamily K Lam)) :=
    OsinWeightedMetric.isPowerTorsionFree_coprodI
      (isPowerTorsionFree_pairFamily hKtf hLtf)
  have hinj0 : Function.Injective (freeProductSourceHom K Lam) :=
    CoprodI.of_injective (M := pairFamily K Lam) false
  have hinj : Function.Injective
      ((MonoidHom.id (CoprodI (pairFamily K Lam))).comp
        (freeProductSourceHom K Lam)) := hinj0
  refine ⟨CoprodI (pairFamily K Lam), inferInstance, MonoidHom.id _,
    Function.surjective_id, inferInstance, htf, hinj, ?_⟩
  intro x _
  exact MonoidHom.mem_range.mpr (hpartner x)

/-! ## 3.  The manuscript's field -/

/-- **`FournierFacioQuotientStatement` from Proposition 2.3.**

One named `Prop`, and it is the one the manuscript's own sentence cites.  Every
step below is bookkeeping:

* non-elementarity of `H₀` is `isNonElementaryHyperbolic_of_kazhdan'`, spending
  `Infinite H₀` and property `(T)` -- the same place they were spent in all four
  earlier generations;
* the prescribed finite set is the image in `U ∗ H₀` of a finite generating set
  of `U`, which `ProductFinitePresentation.fg_of_isFinitelyPresented` supplies;
* `H₀ ↠ P` is `surjective_partner_of_sourceGen` against the clause
  `π(gᵢ) ∈ π(Λ)`, which is the only clause of Proposition 2.3 that is not
  already in the manuscript's shape;
* `U ↪ P` is the injectivity clause verbatim. -/
theorem fournierFacioQuotientStatement_of_prop23
    (hProp : FournierFacioProposition23) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement := by
  intro H₀ U instH₀ instU hinf hfp htf hhyp hT hUfp hUtf
  haveI := hinf
  haveI := hUfp
  have hne : IsNonElementaryHyperbolic H₀ :=
    isNonElementaryHyperbolic_of_kazhdan' hhyp hT
  obtain ⟨S, hSgen, hSfin⟩ :=
    Group.fg_iff.mp (ProductFinitePresentation.fg_of_isFinitelyPresented U)
  have hgfin : (freeProductSourceHom U H₀ '' S).Finite :=
    hSfin.image (freeProductSourceHom U H₀)
  obtain ⟨Q, instQ, pi, hsurj, hQfp, hQtf, hQinj, hQmem⟩ :=
    hProp U H₀ instU instH₀ hne htf hUfp hUtf
      (freeProductSourceHom U H₀ '' S) hgfin
  have hmem : ∀ x ∈ S, pi (freeProductSourceHom U H₀ x)
      ∈ (pi.comp (freeProductPartnerHom U H₀)).range := by
    intro x hx
    have hximg : freeProductSourceHom U H₀ x
        ∈ freeProductSourceHom U H₀ '' S := ⟨x, hx, rfl⟩
    exact hQmem _ hximg
  exact ⟨Q, instQ, hQfp, hQtf,
    ⟨pi.comp (freeProductPartnerHom U H₀),
      surjective_partner_of_sourceGen pi hsurj hSgen hmem⟩,
    ⟨pi.comp (freeProductSourceHom U H₀), hQinj⟩⟩

end RelHyp
end GGT
end GroupApproximation
