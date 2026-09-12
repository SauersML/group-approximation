import GroupApproximation.Algebra.ExchangeRing
import GroupApproximation.Leavitt.PreusserNormalizedBy
import GroupApproximation.Leavitt.PreusserLevelUniqueness
import GroupApproximation.Leavitt.LeavittPurelyInfinite
import GroupApproximation.Leavitt.LeavittSelfSimilarity
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Field.ZMod

/-!
# Preusser's sandwich theorem, with the printed hypothesis

`non_mf_groups_exist.tex`, proof of Theorem `thm:headline`, lines 1131--1140:

> Let `N` be a normal subgroup of `H`.  The ring `R` is purely infinite
> simple~\cite{AbramsAranda} and therefore an exchange
> ring~\cite{AraExchange}, so by Preusser's sandwich
> theorem~\cite[Theorem~3]{Preusser} there is an ideal `I` of `R` with
> `EL_4(R,I) ≤ N ≤ C_4(R,I)`, where `EL_4(R,I)` is the normal closure in
> `EL_4(R)` of the elementary matrices `e_{ij}(a)` with `a ∈ I`, and
> `C_4(R,I)` is the preimage of the center of `GL_4(R/I)`.

`Leavitt/PreusserNormalizedBy.lean` already proves Preusser's Theorem 3 at the
source's own generality, existence and uniqueness together, for every subgroup
of `GL_ι(R)` normalized by `EL_ι(R)` with `3 ≤ card ι`.  Its ring hypothesis is
spelled `ExchangePrerequisite.HasFiniteRightExchangePartitions R` -- the finite
orthogonal refinement Proposition 21 consumes -- rather than the printed
"exchange ring".

This module states the theorem with the printed hypothesis, and then discharges
the whole printed chain at the manuscript's coefficient ring.

## The chain, with nothing assumed

1. `L_k(1,2)` is purely infinite simple in the printed Ara--Goodearl--Pardo
   idempotent form (`binaryLeavitt_isPurelyInfiniteSimpleRing`, from
   single-sandwich division and the binary complete matrix family).
2. Hence it is an exchange ring, by Ara
   (`isExchangeRing_of_isPurelyInfiniteSimpleRing`, `Algebra/ExchangeRing.lean`).
3. Hence Preusser's Theorem 3 applies to it at every rank `n ≥ 3`, and in
   particular at the printed rank `n = 4`.

So `manuscriptSentence_rankFourSandwich` is a closed proposition: the printed
sentence's citations are all proved, not assumed.

## The two objects named in the sentence

They are the tree's `relativeElementary ι I` and `congruenceSubgroup ι I`
(`Leavitt/CongruenceSubgroups.lean`), which are exactly the printed
`EL_n(R,I)` -- the normal closure of the `e_{ij}(a)`, `a ∈ I` -- and the
printed `C_n(R,I)`, the units congruent modulo `I` to a central scalar, the
entrywise form of "preimage of the centre of `GL_n(R/I)`".
-/

namespace GroupApproximation
namespace PreusserSandwichExchange

/-! ### Preusser's Theorem 3 over an exchange ring -/

section General

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **Preusser's Theorem 3**, with the hypothesis spelled as the manuscript
spells it.  For an exchange ring `R` and `3 ≤ card ι`, every subgroup of
`GL_ι(R)` normalized by `EL_ι(R)` has exactly one level ideal `I`, that is,
exactly one two-sided ideal with `EL_ι(R, I) ≤ N ≤ C_ι(R, I)`. -/
theorem preusser_sandwich_of_isExchangeRing (hcard : 3 ≤ Fintype.card ι)
    (hex : IsExchangeRing R) (N : Subgroup (Matrix ι ι R)ˣ)
    (hnorm : ∀ e ∈ elementaryGroup ι R, ∀ h ∈ N, e * h * e⁻¹ ∈ N) :
    ∃! I : TwoSidedIdeal R,
      (relativeElementary ι I).map (elementaryGroup ι R).subtype ≤ N ∧
        N ≤ congruenceSubgroup ι I := by
  obtain ⟨I, hIl, hIu⟩ :=
    PreusserNormalizedBy.preusser_sandwich_normalizedBy hcard
      hex.hasFiniteRightExchangePartitions N hnorm
  refine ⟨I, ⟨hIl, hIu⟩, ?_⟩
  rintro J ⟨hJl, hJu⟩
  exact PreusserNormalizedBy.eq_of_sandwich hcard hJl hJu hIl hIu

/-- The same conclusion for a normal subgroup of `EL_ι(R)`, which is the shape
the printed proof uses: `N ⊴ H = EL_4(R)`.  Here the lower inclusion is read
inside `EL_ι(R)` itself, as the source and the manuscript both write it.

The witness is the canonical level ideal, exactly as in
`PreusserLevel.manuscriptPreusserNormalSubgroupTheorem`; only the ring
hypothesis is restated. -/
theorem preusser_sandwich_normal_of_isExchangeRing (hcard : 3 ≤ Fintype.card ι)
    (hex : IsExchangeRing R) (N : Subgroup (elementaryGroup ι R)) (hN : N.Normal) :
    ∃! I : TwoSidedIdeal R,
      relativeElementary ι I ≤ N ∧
        N.map (elementaryGroup ι R).subtype ≤ congruenceSubgroup ι I := by
  haveI := hN
  refine ⟨normalLevel hcard N,
    ⟨relativeElementary_normalLevel_le hcard N, ?_⟩, ?_⟩
  · exact PreusserAssembly.map_le_congruenceSubgroup_normalLevel hcard
      (PreusserAssembly.prop21Entry hcard hex.hasFiniteRightExchangePartitions)
      (PreusserAssembly.prop21DiagDiff hcard hex.hasFiniteRightExchangePartitions) N
  · rintro J ⟨hJl, hJu⟩
    exact PreusserLevel.eq_normalLevel_of_sandwich hcard N hJl hJu

end General

/-! ### The printed sentence, at the printed generality -/

/-- **Printed:** "by Preusser's sandwich theorem [Pre, Theorem 3] there is an
ideal `I` of `R` with `EL_n(R,I) ≤ N ≤ C_n(R,I)`", for an exchange ring and
`n ≥ 3`.  Uniqueness of `I` is part of the source's statement and is included.

Packaged as a closed `Prop`: a theorem carrying the ring, the rank bound, the
exchange hypothesis and the subgroup in front of the colon is conditional
however clean its proof is. -/
def PreusserSandwichTheoremForExchangeRings : Prop :=
  ∀ (ι R : Type) [Fintype ι] [DecidableEq ι] [Ring R],
    3 ≤ Fintype.card ι → IsExchangeRing R →
    ∀ (N : Subgroup (Matrix ι ι R)ˣ),
      (∀ e ∈ elementaryGroup ι R, ∀ h ∈ N, e * h * e⁻¹ ∈ N) →
      ∃! I : TwoSidedIdeal R,
        (relativeElementary ι I).map (elementaryGroup ι R).subtype ≤ N ∧
          N ≤ congruenceSubgroup ι I

/-- Closed proof of Preusser's Theorem 3 over an exchange ring. -/
theorem manuscriptSentence_preusserSandwichForExchangeRings :
    PreusserSandwichTheoremForExchangeRings := by
  intro ι R _ _ _ hcard hex N hnorm
  exact preusser_sandwich_of_isExchangeRing hcard hex N hnorm

/-! ### The manuscript's coefficient ring

`R = L_{𝔽₂}(1,2)`, at which the printed chain is discharged end to end. -/

section BinaryLeavitt

variable (k : Type) [Field k]

/-- **`L_k(1,2)` is purely infinite simple** in the printed Ara--Goodearl--Pardo
idempotent form, for every field `k` (Abrams--Aranda Pino).

The binary Leavitt family is a complete matrix family on two indices, so it
supplies the proper isometry, and single-sandwich division supplies both the
simplicity and the sandwich clause. -/
theorem binaryLeavitt_isPurelyInfiniteSimpleRing :
    MFQuotientUnits.IsPurelyInfiniteSimpleRing
      (BinaryLeavitt.BinaryLeavittAlgebra k) :=
  LeavittPurelyInfinite.isPurelyInfiniteSimpleRing_of_completeMatrixFamily
    (LeavittFamily.binaryMatrixFamily (BinaryLeavitt.family k))
    (show (0 : Fin 2) ≠ 1 by decide)
    (BinaryLeavitt.hasSingleSandwichDivision k)

/-- **`L_k(1,2)` is an exchange ring**, by Ara's theorem applied to the
previous line.  This is the printed inference "purely infinite simple, and
therefore an exchange ring", carried out on the manuscript's ring. -/
theorem binaryLeavitt_isExchangeRing :
    IsExchangeRing (BinaryLeavitt.BinaryLeavittAlgebra k) :=
  isExchangeRing_of_isPurelyInfiniteSimpleRing
    (binaryLeavitt_isPurelyInfiniteSimpleRing k)

/-- Preusser's Theorem 3 at `L_k(1,2)`, every rank `n ≥ 3`, with every
hypothesis of the printed sentence discharged. -/
theorem preusser_sandwich_binaryLeavitt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (Matrix ι ι (BinaryLeavitt.BinaryLeavittAlgebra k))ˣ)
    (hnorm : ∀ e ∈ elementaryGroup ι (BinaryLeavitt.BinaryLeavittAlgebra k),
      ∀ h ∈ N, e * h * e⁻¹ ∈ N) :
    ∃! I : TwoSidedIdeal (BinaryLeavitt.BinaryLeavittAlgebra k),
      (relativeElementary ι I).map
          (elementaryGroup ι (BinaryLeavitt.BinaryLeavittAlgebra k)).subtype ≤ N ∧
        N ≤ congruenceSubgroup ι I :=
  preusser_sandwich_of_isExchangeRing hcard (binaryLeavitt_isExchangeRing k) N hnorm

end BinaryLeavitt

/-! ### The printed application, at `R = L_{𝔽₂}(1,2)` and `n = 4` -/

/-- **Printed:** "Let `N` be a normal subgroup of `H`.  The ring `R` is purely
infinite simple and therefore an exchange ring, so by Preusser's sandwich
theorem there is an ideal `I` of `R` with `EL_4(R,I) ≤ N ≤ C_4(R,I)`."

Stated for every subgroup of `GL_4(R)` normalized by `EL_4(R)`, which contains
the printed case `N ⊴ H = EL_4(R)`; uniqueness of `I` is included. -/
def PrintedRankFourSandwich : Prop :=
  ∀ (N : Subgroup (Matrix (Fin 4) (Fin 4)
      (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))ˣ),
    (∀ e ∈ elementaryGroup (Fin 4) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
      ∀ h ∈ N, e * h * e⁻¹ ∈ N) →
    ∃! I : TwoSidedIdeal (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)),
      (relativeElementary (Fin 4) I).map
          (elementaryGroup (Fin 4)
            (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).subtype ≤ N ∧
        N ≤ congruenceSubgroup (Fin 4) I

/-- Closed proof of the printed sentence: purely infinite simple, hence
exchange, hence Preusser's sandwich, all three steps proved. -/
theorem manuscriptSentence_rankFourSandwich : PrintedRankFourSandwich := by
  intro N hnorm
  exact preusser_sandwich_binaryLeavitt (ZMod 2)
    (by norm_num : 3 ≤ Fintype.card (Fin 4)) N hnorm

end PreusserSandwichExchange
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms
  GroupApproximation.PreusserSandwichExchange.preusser_sandwich_of_isExchangeRing
#audit_axioms
  GroupApproximation.PreusserSandwichExchange.binaryLeavitt_isExchangeRing
#audit_closed_axioms
  GroupApproximation.PreusserSandwichExchange.manuscriptSentence_preusserSandwichForExchangeRings
#audit_closed_axioms
  GroupApproximation.PreusserSandwichExchange.manuscriptSentence_rankFourSandwich
