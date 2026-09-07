# Lane `rank-four`: `thm:headline` at `H = EL_4(L_{F_2}(1,2))`

Task: re-create at rank four everything the rank-twelve modules prove for
`EL_12`, as new modules, without touching the rank-twelve ones.

## Landed

| commit | modules | jobs |
|---|---|---|
| `bd0e81062f43b5189f5433777249ad70bdc80d76` | `RankFourEndpoints.lean`, `RankFourSimplicity.lean` | 4383 / 4450 |
| `7908cd9bcd9ea4ed1f1fce22955948536334a472` | `RankFourConfiguration.lean`, `RankFourEJZInstance.lean` | 4389 |
| `81202607aa74ff1ea93b5801ade49bf98a454ac0` | `HeadlineTheoremRankFour.lean`, `ReducedCStarConsequenceRankFour.lean`, `RankFourAudit.lean` | 4464 / 4470 |
| `acea48a28f00f7edda9877000c114d1adb600d5a` | `RankFourOneSidedBridge.lean` | 4388 |

All under `GroupApproximation/Manuscript/OneSidedMFRadical/`, namespace
`GroupApproximation.Manuscript.OneSidedMFRadical.RankFourEndpoint` (the
headline and C⋆ modules live one namespace up, as at rank twelve).  The root
import list is the lead's to wire.

## The printed endpoints and their carriers

| printed | carrier |
|---|---|
| `thm:headline`, whole | `manuscriptPrintedHeadlineRankFour` |
| `thm:headline`, group clauses | `manuscriptBinaryLeavittHeadlineRankFour` |
| `thm:headline`, radical package | `manuscriptBinaryLeavittFullRadicalRankFour` |
| `thm:headline`, reduced-C⋆ clause | `manuscriptReducedCStarConsequenceRankFour` |
| `thm:headline`, maximal-C⋆ clause | `manuscriptMaximalCStarNotFiniteRankFour` |
| Blackadar–Kirchberg refutation form | `manuscriptNotEverySeparableStablyFiniteCStarAlgebraIsMFRankFour` |
| `prop:simple` | `RankFourEndpoint.manuscriptPropositionSimple` |
| compression step of `thm:full-defect-ring` at `R` | `RankFourEndpoint.manuscriptPropositionDefect` |
| `Rad_MF(H) = H` | `RankFourEndpoint.rankFour_actualCoronaMFResidual_eq_top` |
| "Both groups have property (T)" (EJZ) | `RankFourEndpoint.printedBothGroupsHaveKazhdanPropertyT` |
| strictness `uLu⁻¹ ⊊ L` | `RankFourEndpoint.u_conj_corner_lt` |

## What is rank-four-specific

The printed mark is `c = [e₄₁(e), e₁₄(t)] = diag(1,1,1,1+et)`.  At rank four it
cannot be an elementary root: every index pair meets the corner `{1,2,3}`.  So
`RankFourEndpoint.c` is a commutator, its matrix value is a calculation
(`c_val`), and its centrality relative to the corner is a calculation rather
than the disjoint-support argument used at rank twelve.  Accordingly
`PrintedDefectConfiguration` has four conjuncts here, not three: property (T)
for the corner, centrality of `c`, the compression `uLu⁻¹ ≤ L`, and the
commutator `[ucu⁻¹, ℓ] = d`.

Nothing else is rank-specific.  The compressor `u = u₃u₂u₁` and the conjugation
identity are already in `Leavitt/RankFourCompressors.lean`; normal generation of
the defect, root detection, simplicity, the compression criterion, and the two
C⋆ clauses all ask only for three indices or for nothing at all.

## Deviations from the brief

1. `corner_hasKazhdanPropertyT` and the corner-embedding machinery live in
   `RankFourEndpoints`, not `RankFourConfiguration`, so that
   `RankFourEJZInstance` can state its agreement lemma without waiting for the
   configuration.
2. The configuration was built directly on `Leavitt/RankFourCompressors.lean`
   rather than on lane `ring-b-alg`'s `OneSidedCompressor.lean`, which had not
   landed at the time.  It has since landed, and `RankFourOneSidedBridge.lean`
   reconciles the two: `corner = OneSidedCompressor.core R`,
   `u = OneSidedCompressor.compressor (ofLeavittFamily leavittFamily)`,
   `c = centralMark …`, `ell = printedEll R`, `defect = printedDefectRoot …`.
   All five are definitional except the two involving the complementary
   idempotent, which the two developments spell `s₁t₁` and `1 - s₀t₀`.  So
   there is one rank-four corner under two names, not two corners, and
   `printedDefect_core_eq_top` states the saturation in
   `OneSidedCompressor`'s own vocabulary.
3. The maximal-C⋆ clause is *inside* `PrintedHeadlineRankFour`.  At rank twelve
   it was proved (in `PrintedLeavittEquations`) but left out of the headline
   package, which the manifest wrongly called complete.

## Traps worth reusing

* `Subgroup.closure_induction` over the *subgroup-subtype* group structure
  times out in `whnf` at 200000 heartbeats here, and does so even when the
  statement is generic in the coefficient ring, because every step needs a
  `change` across `⟨x, hx⟩ * ⟨y, hy⟩`.  Going through
  `elementaryRootSet_generate` plus `Subgroup.closure_le` avoids the issue
  entirely and is shorter.
* `HilbertHotel.normalClosure_elementaryRoot_eq_top` needs rank `≥ 5` and is
  unusable at rank four.  `normalClosure_elementaryRoot_p1_eq_top` and
  `elementaryGroup_normal_eq_top_of_elementaryRoot_mem` need only three
  indices and hold over every ring with a binary Leavitt family.
* `mul_assoc` in a `simp` set right-associates every product, so a relation
  like `t₀ * e = 0` never appears as a subterm of a longer word.  The
  absorbing form `∀ x, t₀ * (e * x) = 0` has to be supplied alongside it, and
  the `unusedSimpArgs` linter (an error under `-DwarningAsError=true`) is what
  tells you which of the two actually fired.

## Open

Nothing in the brief is open, and the lead's follow-up bridging lemma
(`compressor_eq_oneSidedCompressor`) is landed.  The one thing outside it: the `\leanverified`
lines of `thm:headline` in `non_mf_groups_exist.tex` still name the
rank-twelve declarations, and the manifest and census rows still point there.
Those are the lead's and the tex peer's to repoint at the names in the table
above.
