# cite-ejz lane report (2026-09-12)

Task: fully and unconditionally formalize the five sentences of `non_mf_groups_exist.tex` that cite
`\cite[Theorem~1.1]{EJZ}`, with no literature inputs.

## Verdict

EJZ Theorem 1.1 is PROVED at the generality the paper uses. The proof is
`IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT : FinitelyGeneratedRingGeneralRankElementaryPropertyT`:
for every finitely generated unital ring `A : Type` and every `n ≥ 3`, `EL_n(A)` has (T).
- Module: PropertyT/IntegralColumnPlaneClosure.
- Audit: `#audit_closed_axioms`.
- Last edit cfde48701; root-wired in 7cbc25e4c.

It is not an input anywhere on the manuscript route:
- The binder `hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT` occurs only in intermediate `…FromEJZ` theorems.
- Every tex badge points at the discharged form in `FullDefectRingEJZUnconditional`, via `ejz := IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`.
- kh-ejz owns GHB(7) property (T) (tex 1675), not this theorem.

No module in the import closures of the endpoints below has changed on origin since the last root wire, bfbe000c7.

## Per sentence

1. **tex 939–943** (proof of thm:full-defect-ring): "The ring 𝒞 is nonzero, since it maps onto
   L_{F_2}(1,2), and finitely generated, so both groups have property (T) by [EJZ, Theorem 1.1], and
   EL_4(𝒞) is finitely generated [BHV, Theorem 1.3.1]."
   - **CLOSED at the printed L:** `EJZCitationSentences.manuscriptSentence_universalRingBothGroupsPropertyT`.
     - Covers all of: surjection onto L_F2(1,2), 𝒞 nontrivial, 𝒞 f.g., (T) for G = EL_4(𝒞), (T) for L = core on
       coordinates 1,2,3, and G f.g.
     - Landed e8057db8a; PROBE GREEN 0912-105047-81911; closed audit; not yet root-wired.
   - Earlier form, where the second group is the abstract EL_3(𝒞):
     `UniversalRingSentences.manuscriptSentence_universalRingPrintedReasons`.
     - Landed c043f3fc4; probe 0911-210130-73901 PROBE GREEN; root-wired 4a49dba9c.
2. **tex 1051–1056** (proof of cor:one-sided-ring-maximal): "then L has property (T) [EJZ, Theorem 1.1],
   and the compression is strict".
   - **CLOSED:** `HeadlineCitationSentences.manuscriptSentence_pairSubringElementaryPropertyT` (closed audit).
   - The core form is `TorsionComplementaryIdempotents.manuscriptSentence_pairSubringCoreKazhdan`.
   - Strictness: `OneSidedCorollarySentences.manuscriptSentence_strictCompressionWitness`.
   - Landed a686eaa56; probe 0911-204106-71715; root-reachable.
3. **tex 1084–1087** (proof of prop:torsion-defect-ring): "let L=EL_3(S) occupy coordinates 1,2,3 of
   EL_4(S); it has property (T) [EJZ, Theorem 1.1]."
   - **CLOSED:** `TorsionComplementaryIdempotents.manuscriptSentence_pairSubringCoreKazhdan` (closed audit).
   - Landed 19e04b189 (compiled); root-wired 4a49dba9c.
4. **tex 1155–1157** (remark on J = F_2⟨s,t | ts=1⟩): "Three coordinates carry property (T) [EJZ, Theorem 1.1],
   and the fourth makes the compression by s invertible."
   - **OWNED BY jacobson:** `JacobsonRankFour.manuscriptSentence_threeCoordinatesCarryPropertyT` and
     `…fourthCoordinateMakesCompressionInvertible`.
     - Stated for every f.g. ring and every pair; `#audit_axioms`.
     - Landed 8e0bf35e2; probe 0911-204249-81394; root-wired 4a49dba9c.
   - **CLOSED at the printed J** (first half):
     `EJZCitationSentences.manuscriptSentence_jacobsonThreeCoordinatesCarryPropertyT`.
     - J = `jacobsonAlgebra` is f.g., and the core EL_3(J) inside EL_4(J) has (T).
     - Landed e8057db8a; PROBE GREEN 0912-105047-81911; closed audit. jacobson informed.
5. **tex 1170–1175** (proof of thm:headline): "The ring R is finitely generated, so H has property (T) by
   [EJZ, Theorem 1.1], and hence is finitely generated [BHV, Theorem 1.3.1]."
   - **CLOSED**, all closed audits:
     - `HeadlineCitationSentences.manuscriptSentence_finitelyGeneratedGivesPropertyT`
     - `HeadlineCitationSentences.manuscriptSentence_propertyTGivesFinitelyGenerated`
     - `HeadlineCitationSentences.headlineGroup_finitelyGenerated_via_propertyT`
   - Last edit 7b66deac0; root-reachable through UniversalRingSentences (4a49dba9c).

Nothing is IN PROGRESS, and this cluster has no open leaves.

## Files owned

- `GroupApproximation/Manuscript/NonMFSentences/EJZCitationSentences.lean`
  - Landed e8057db8a; PROBE GREEN 0912-105047-81911 (BUILT + COMPILED); origin identical to the green copy.
  - Wire candidate; it imports only root-wired modules.

## Census rows (metadata/nm-census-rows/cite-ejz.tsv)

- LINE:939 `formalized`: `EJZCitationSentences.manuscriptSentence_universalRingBothGroupsPropertyT`.
- LINE:1155 `partial`: `EJZCitationSentences.manuscriptSentence_jacobsonThreeCoordinatesCarryPropertyT`.
  - Only the EJZ half; the jacobson row carries the whole sentence.

## Commits

- e8057db8a: EJZCitationSentences.lean (green content).
- eba86ccbf: first version of this report.
