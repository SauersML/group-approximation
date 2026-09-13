# Lane ct-rank-budget: cor:dynamic-rank-budget (tex 1696–1767) and the Introduction aperiodic sentence

Snapshot: origin/main 2715b4830 (09-13; tex unchanged since 73a84cd9c).  Roster: ct lead session (not the
every-line coordinator).  This file is written by ct-rank-budget only.

## Printed items owned

- cor:dynamic-rank-budget statement (tex 1696–1705): no fixed points ⇒ over any finite field `GL_n(R_X)`,
  `EL_n(R_X)` (n ≥ 2) MF ⟺ LEF ⟺ `R_X` directly finite; no points of period one or two ⇒ the same for `R_X^×`;
  over `F_2` all these MF radicals are the locally finite core restriction kernels; aperiodic ⇒ the maximal MF
  quotient of `R_X^×` is its LEF restriction image on the chain-recurrent core.
- Its proof, tex 1743–1766: the induced core `C ∩ Y`; the return transient ideal `J = p_C I p_C`; the `F_2` radical
  equality; the transfer over other finite fields; the positive implications.
- Introduction (tex 254–256): "If T is aperiodic, the same conclusion holds already for the unit group and for every
  elementary rank n ≥ 2."
- The tower half of the proof (tex 1707–1741) belongs to ct-return-tower; the involution lemma to ct-involution;
  prop:bilateral-three to ct-bilateral-mf; thm:core-mf-radical to chain-radical; thm:core-ring-reflection to
  chain-reflection.

## Planned modules (unwired; each small, probed and landed alone)

1. `GroupApproximation/Manuscript/OneSidedMFRadical/MFRadicalTransport.lean` — no upstream.  The group- and
   ring-generic steps of the printed proof:
   - `map_mfHomKernel_le`: a homomorphism carries the MF radical into the MF radical (the embedded group's kill
     passes to `GL_n(R_X)`, tex 1752–1755);
   - `mem_mfHomKernel_of_conj_mem`, `le_mfHomKernel_of_conj_mem_map`: conjugation into an embedded radical kills
     (tex 1756–1757);
   - `mfHomKernel_le_ker`, `mfHomKernel_eq_bot_of_isOperatorMF`, `mfHomKernel_eq_ker_of_le`: the radical sandwich
     ("core restriction has LEF image, giving equality of radicals", tex 1757–1758), and
     `quotientMFRadicalEquivRange` (the maximal MF quotient is the restriction image, tex 1703–1704);
   - `not_isOperatorMF_of_injective_of_mem`: a nonzero invisible root transferred along an injective embedding
     (tex 1763–1765);
   - `isDedekindFiniteMonoid_of_injective_nonUnitalRingHom`: "the full tower corner would make `R_X` directly
     finite" (tex 1761–1763);
   - `isOperatorMF_iff_isLEF_and_isLEF_iff_of_pieces`: MF ⟺ LEF ⟺ directly finite from (DF ⇒ LEF ring),
     (LEF ring ⇒ LEF group), (not DF ⇒ nontrivial radical).
2. `GroupApproximation/Manuscript/NonMFSentences/DynamicRankBudget.lean` — after chain-core's `restrict`
   (ClopenCrossedProductComap, probe GREEN 0913-162119-82055) lands.  `def PrintedDynamicRankBudget : Prop` over
   `ClopenCrossedProduct T k`, `Dynamics.chainRecurrentSet`, `ClopenCrossedProduct.restrict`; the assembly
   `printedDynamicRankBudget_of_pieces` over the named piece Props below.
3. My pieces, then: induced core `C ∩ Y`; `J = p_C I p_C`; the Introduction sentence.

## Piece Props consumed (owner)

| Prop (planned name here) | content | owner |
|---|---|---|
| `ReturnTowerStatement` | full section `C` with gaps in `[r, 2r−1]`; `P_C ≅ R_{(C, S_C)}`; `Φ`; unitization embeddings | ct-return-tower |
| `InvolutionLocalizationStatement` | lem:involution-localization | ct-involution |
| `BilateralThreeStatement` | prop:bilateral-three | ct-bilateral-mf |
| `CoreMFRadicalStatement` | thm:core-mf-radical (`F_2`), incl. kernel identification | chain-radical |
| `CoreRingReflectionStatement` | thm:core-ring-reflection | chain-reflection |
| prop:torsion-defect-ring | `manuscriptTorsionComplementaryIdempotents` (closed on main) | — |

## Progress log

- 09-13 ~16:35: plan landed (this file).  Module 1 authored; probing.
