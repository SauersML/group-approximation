import GroupApproximation.GGT.RelHypProp23FromOsin24
import GroupApproximation.GGT.RelHypSuitabilityClosure
import GroupApproximation.GGT.HullYiStatements

/-!
# The sharp faithful reduction of Fournier--Facio Proposition 2.3

The source-faithful quotient statement does not follow from the elementary
free-product bookkeeping alone.  This module records the narrowest reduction
currently supported by the formalized geometry:

* Osin's Theorem 2.4, including the finite-normal-generation clause read from
  its proof; and
* the existence of two non-commensurable infinite-order elements in every
  torsion-free non-elementary hyperbolic group.

The other half of suitability -- trivial intersection of the two Osin
elementary closures -- is already unconditional, via
`hyperbolicElementaryClosureStatement`.  Thus it is deliberately absent from
the hypotheses below.

This is not an unconditional proof of the literature theorem.  It is a
code-checked boundary: any such proof must replace the two arguments below,
not the already-closed algebraic and elementary-closure layers.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## The pair leaf is shared with Hull's `yi` construction -/

/-- Hull's source-faithful `yi` pair supplies the non-commensurable pair used
by Fournier--Facio.

To apply `yi`, equip the hyperbolic group with its finite Cayley alphabet.  A
direct-power-separated pair gives an element outside one elementary closure,
so the existing finite-Cayley construction makes this alphabet a
`HullGeneratingSet`.  Its whole subgroup is suitable because the ambient group
is torsion-free.  The conjugator-sensitive non-commensurability returned by
`yi` is then exactly `¬ OsinCommensurable`.

Thus the Hull cone-off leaf and the Fournier--Facio pair leaf do not require two
independent literature inputs: they share the single product-word construction
inside `YiSuitablePair`. -/
theorem hyperbolicNonCommensurablePairStatement_of_yi
    (hyi : HullSC.YiSuitablePair.{0}) : HyperbolicNonCommensurablePairStatement := by
  intro H instH hne htf
  letI := instH
  obtain ⟨T, hT, delta, hdelta⟩ := hne.1
  let A : Alphabet H := ⟨(T : Set H), hT⟩
  have hAfin : A.carrier.Finite := T.finite_toSet
  have hAδ : IsHyperbolicSpace (delta : ℝ) (Cayley A) :=
    isHyperbolicSpace_cayley_of_fourPoint A hdelta
  obtain ⟨g, t, hgord, htord, hsep⟩ :=
    exists_infiniteOrder_pair_no_common_zpow hne htf
  have hg1 : g ≠ 1 := by
    intro hg
    exact hgord 1 one_pos (by simp [hg])
  have ht1 : t ≠ 1 := by
    intro ht
    exact htord 1 one_pos (by simp [ht])
  have hgfin : ¬ IsOfFinOrder g := htf.not_isOfFinOrder hg1
  have htout : t ∉ GGT.Elementary.elementaryClosure g :=
    HullSCUnionGeometry.notMem_elementaryClosure_of_no_common_zpow
      A hAfin hAδ htf hgfin hsep ht1
  let B : HullGeneratingSet H :=
    HullSCUnionGeometry.hullGeneratingSetOfWitness hT hdelta hgfin htout
  have hsuitable : Suitable B.alphabet (⊤ : Subgroup H) :=
    ⟨B.nonElementary,
      HullSuitable.normalizesNoNontrivialFinite_of_torsionFree htf ⊤⟩
  obtain ⟨f, _hfmem, hflox, hfnc, _hfcyc⟩ := hyi B hsuitable
  have hford : ∀ b : Bool, ∀ n : ℕ, 0 < n → f b ^ n ≠ 1 := by
    intro b n hn hpow
    exact not_isOfFinOrder_of_isLoxodromic (hflox b)
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩)
  refine ⟨f false, f true, hford false, hford true, ?_⟩
  rintro ⟨p, q, c, hp, hq, heq⟩
  exact hfnc c p q hp hq heq

/-- The faithful Fournier--Facio proposition follows from the exact Osin
quotient theorem and the only still-open half of hyperbolic suitability.

Unlike the retired `OsinTheorem24Final` route, this invokes the verbatim
Theorem 2.4 interface and does not postulate a false universal relator design.
-/
theorem fournierFacioProposition23_of_osin24_of_nonCommensurablePair
    (hOsin : OsinTheorem24FinitePresentationAddendum)
    (hPair : HyperbolicNonCommensurablePairStatement) :
    FournierFacioProposition23 :=
  fournierFacioProposition23_of_osin24 hOsin
    (hyperbolicSuitabilityStatement_of_nonCommensurablePair hPair)

/-- The manuscript's quotient field at the same sharp boundary. -/
theorem fournierFacioQuotientStatement_of_osin24_of_nonCommensurablePair
    (hOsin : OsinTheorem24FinitePresentationAddendum)
    (hPair : HyperbolicNonCommensurablePairStatement) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement :=
  fournierFacioQuotientStatement_of_prop23
    (fournierFacioProposition23_of_osin24_of_nonCommensurablePair hOsin hPair)

/-- The manuscript quotient statement from the two genuinely shared source
leaves: Osin's quotient theorem and Hull's `yi` product-word construction. -/
theorem fournierFacioQuotientStatement_of_osin24_of_yi
    (hOsin : OsinTheorem24FinitePresentationAddendum)
    (hyi : HullSC.YiSuitablePair.{0}) :
    Manuscript.NonMF.TheoremC.FournierFacioQuotientStatement :=
  fournierFacioQuotientStatement_of_osin24_of_nonCommensurablePair hOsin
    (hyperbolicNonCommensurablePairStatement_of_yi hyi)

end RelHyp
end GGT
end GroupApproximation
