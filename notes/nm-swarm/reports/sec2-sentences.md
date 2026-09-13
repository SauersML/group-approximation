# sec2-sentences: Section 2 "One-sided compression" (tex 346-784 at 73c867c5b)

Status 2026-09-11 22:40: **done**.  Every non-structural sentence of Section 2 has a carrier that compiled.
None of these modules is imported by the root yet; they are queued for wiring.

## Modules (all `GroupApproximation/Manuscript/NonMFSentences/`)

| module | carries | landed (compiled) |
|---|---|---|
| CompressionSentencesA | prop:mf-residual-calculus proof sentences; canonical maps into U(C*max(G)), U(C*r(G)); Ad(V(g)) bijection; finite / stably finite | 1b3021bfe (probe 0911-210656) |
| CompressionSentencesB | τ = lim_ω tr_{r_n} well defined, linear, unital, positive, tracial (representatives) | f88d7583 (0911-212711) |
| CompressionSentencesB2 | τ as a continuous linear functional on the corona 𝒬_r, \|τ(x)\| ≤ ‖x‖ | a0ff25d62 (0911-214558) |
| TransportCharacterizationIffSentence | x ∈ 𝒞₂(V,L) iff ‖P_n x_n − x_n‖₂ → 0 | 3d48bf8ef (0911-212047) |
| CentralCoronaCornerRanks | retained coordinates, r_n = rank(q_n) ≥ 1 | 3d48bf8ef (0911-212047) |
| HSOperatorNormGapSentences | ‖D_d − 1‖₂ = 2/√d → 0, ‖D_d − 1‖ = 2 | 1b3021bfe (0911-212711) |
| KazhdanProjectionExistenceSentence | e_L central star projection fixing exactly the invariant vectors in every representation, every universe | f88d7583 (0911-212711) |
| MFRadicalQuotientBlockSumSentences | tex 372-379: the block-sum family, asymptotically multiplicative, separating; G/Rad_MF(G) has trivial residual | a0ff25d62 (0911-214558) |
| HSNullNormalSubgroupSentences | tex 404-412 with every clause and the three displays; the normal subgroup = hsKernel | 477ebb4a1 (0911-220408) |
| DyadicReductionSeparation | ℤ[1/2] →+* ℤ/m (m odd), V →* GL₄(ℤ/m) separates V, so V is RF and MF | 477ebb4a1 (0911-220408) |
| NormalKazhdanUltrafilterRoute | thm:normal-kazhdan, last paragraph sentence by sentence; endpoint `manuscriptNormalKazhdanRadical_ultrafilterRoute : NormalKazhdanRadical` | 4bc478e03 (0911-221323) |

`DyadicReductionSeparation` imports `Sofic/AffineHNNBaseRealization`, which is also not wired.

## GHW Theorem 4 (tex 1146-1147)

Status 2026-09-12 09:25.  Printed sentence: "Every countable subgroup of $\mathrm{GL}_2$ over a field has the
Haagerup property~\cite[Theorem~4]{GHW}".  No literature inputs are allowed, so the theorem is proved in Lean.  sec2 owns
the modules below.  The Minkowski and Walls modules belong to dgo-geometric; the non-archimedean steps (1)-(5) belong
to jacobson, except step (4), which sec2 wrote.

| module | carries | state |
|---|---|---|
| Kazhdan/GHWArchimedeanWedge | wedge geometry at the archimedean places | compiled (4197466c8) |
| Kazhdan/GHWArchimedeanSeparation | spectral reduction; `SeparationFinite` for every g; κ·\|log a\| ≤ μ(Δ) with κ = 2φ(1) | compiled: probe 0912-093859-21657 BUILT at 448d1bf45 (base 0ac9f4538) |
| Kazhdan/GHWArchimedeanBound | adapters `archimedeanAffineBound_places(_fin)` compiled; `separationFinite`, `ghwArchimedeanAffineBound` | compiled: probe 0912-094259-57545 GREEN at 6d8971521 (base 9b29a2730); both endpoints pass `#audit_closed_axioms` |
| Algebra/GHWFrobeniusSeparable | step (4): `GroupApproximation.GHW.exists_separable_frobenius_embedding` | compiled: probe 0912-092155-16446 GREEN at base 87ab7e225; axioms propext, Classical.choice, Quot.sound |

Step (4), exact statement:
`theorem GroupApproximation.GHW.exists_separable_frobenius_embedding (L K : Type*) [Field L] [Field K] [Algebra L K]
[FiniteDimensional L K] (p : ℕ) [ExpChar L p] : ∃ (K' : IntermediateField L K) (e : ℕ) (φ : K →+* K'),
Algebra.IsSeparable L K' ∧ ∀ x : K, ((φ x : K') : K) = x ^ p ^ e`.
The proof takes K' := separableClosure L K and e := the exponent of K / K'.  The map φ is
`IsPurelyInseparable.iterateFrobenius`.

Proved without hypotheses (probe 0912-094259-57545; the axioms of both are within the classical allowlist):
`GroupApproximation.GHW.separationFinite : Walls.SeparationFinite` and
`GroupApproximation.GHW.ghwArchimedeanAffineBound : GHWArchimedeanAffineBound`.  Through `archimedeanAffineBound_places_fin`
the second discharges the `(A, hA)` input of `hasHaagerupProperty_of_places`.  Separation and Bound are not root-wired.
Algebra/GHWFrobeniusSeparable is in the root-wiring wave; edits to it land with NM_ATTIC until a probe is green.

## GHW char 0: countably many places

Status 2026-09-12.  The lead assigned sec2 one whole file of the char-0 half.  dgo-geometric owns GHWCharZeroFiniteness
and GHWCharZero and agreed the statements below; jacobson owns char p.  A finite set of σ does not suffice: for ℤ[t] the
finiteness hypothesis of `hasHaagerupProperty_of_places` fails.  So the σ are countable, with bounds that depend on
the place.

| module | carries | state |
|---|---|---|
| Kazhdan/GHWCountablePlaces | `AffineAction.smul`, `countableSum`, `exists_weights`; `Haagerup.hasHaagerupProperty_of_countable_sum`; `GHW.hasHaagerupProperty_of_countable_places` | compiled: probe 0912-102206-8083 GREEN at base 2cc8cb4a7, which contains the landing commit 3a0808fa5 (md5 d9fa48bed4d981ce7837349b9eb2d73d); all three `#audit_axioms` give propext, Classical.choice, Quot.sound |

Exact statements:
`theorem GroupApproximation.Haagerup.hasHaagerupProperty_of_countable_sum {G : Type u} [Group G] [Countable G]
{ι : Type} [Countable ι] (A : ι → AffineAction.{u, v} G)
(hproper : ∀ C : ι → ℝ, {g : G | ∀ i, ‖(A i).b g‖ ≤ C i}.Finite) : HasHaagerupProperty.{u, v} G`

`theorem GroupApproximation.GHW.hasHaagerupProperty_of_countable_places {K : Type} [Field K] {Γ : Type} [Group Γ]
[Countable Γ] (ρ : Γ →* GL (Fin 2) K) (hρ : Function.Injective ρ) {k : ℕ}
(v : Fin k → AddValuation K (WithTop ℤ)) (π : Fin k → K) (hπ : ∀ j, v j (π j) = 1)
{ι : Type} [Countable ι] (σ : ι → (K →+* ℂ)) (S : Set K)
(hS : ∀ (γ : Γ) (a b : Fin 2), ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b ∈ S)
(hfin : ∀ (C : ι → ℝ) (N : ℕ), {a : K | a ∈ S ∧ (∀ i, ‖σ i a‖ ≤ C i) ∧
∀ j, (((-(N : ℤ)) : ℤ) : WithTop ℤ) ≤ v j a}.Finite) : HasHaagerupProperty.{0, 0} Γ`

Weights: enumerate G by e and inject ι into ℕ by f.  Put M_i = ∑_{k ≤ f i} ‖b_i(e k)‖ and w_i = 2^{-f i}/(1 + M_i).
Then (w_i b_i(g))_i is in ℓ².  A bound ‖b g‖ ≤ R gives ‖b_i g‖ ≤ R/w_i for every i.

Wiring (2026-09-13): `GroupApproximation.Kazhdan.GHWCountablePlaces sec2-sentences 3a0808fa5` is in the wire queue.
Nothing it imports has changed since the green base 2cc8cb4a7.  The unwired modules it imports have to be wired first:
GHWInterfaces, GHWArchimedeanWalls and GHWArchimedeanMinkowski (dgo-geometric), GHWArchimedeanWedge, and
GHWArchimedeanSeparation (448d1bf45) and GHWArchimedeanBound (6d8971521).

## Introduction, tex 187-205 (row 61827aea7807): limiting trace and footnote

Status 2026-09-13.  The row is shared with hs-vanishes, which owns `NormalKazhdanPrintedRoute`.  The previous row cited
that route and `CompressionCriterionSentences`, and graded the row partial.  The module below carries the sentence
along the printed ultrafilter route, and the footnote clause by clause.

| module | carries | state |
|---|---|---|
| NonMFSentences/LimitingTraceTrivialCharacterSentence | `PrintedLimitingTraceIsTrivialCharacter`, `PrintedCompressionOutlineFootnote` and their theorems | compiled: probe 0913-014750-80072 GREEN at 0a8ef789f (base cf3dcb3fe); both endpoints pass `#audit_closed_axioms`; queued for wiring |

Sentence (tex 199-201).  Hypotheses: L has (T); K ≤ 𝔇_G(L) is normal with (T); D is corner data; π : C*max(K) → 𝒬_r
agrees with Θ̂ on K; ω is a free ultrafilter.  Conclusion: τ∘π = χ on C*max(K), K has a Kazhdan datum, and every Kazhdan
projection e_K has χ(e_K) = 1 = τ(π(e_K)).  The step "the first step applies" is `printedDefect_le_opToHSShadowResidual_direct`,
which is cor:defect-hs in radical form.

Footnote (tex 201-205), three clauses:
(1) Unitaries can be close in HS norm while their conjugation maps are at operator norm distance 2, and no modulus bounds
one distance by the other (HilbertSchmidtAdjointGap).
(2) W of sec:amenable-nonqd is sofic; the level-zero copy of Γ̄ and ⟨ε⟩ have (T); ⟨ε⟩ ≤ 𝔇_W(L) and ε ≠ 1; and a
unitary HS asymptotic representation of W does not send ε to 1.
(3) The sofic and hyperlinear conclusions fail (CliffordWitnessHSRemark).

## Stale TheoremC docstrings after 2c3c8cb40 (2026-09-13)

The lead's assignment covers three things:
- docstrings that still name the 19 TheoremCAssembly declarations retired in 2c3c8cb40;
- `scripts/TheoremCCompletionAudit.lean`;
- row c6172bdc109a of MF_RECOGNITION_SENTENCE_MAP.

Every change is to documentation only, and each points to the current carrier:
- Theorem C: `TheoremC.manuscriptTorsionFreeFullMFRadical_of_leastAreaInputs` and `..Simplified_of_leastAreaInputs`, over
  `hgreendlinger`, `hbridge` and `hKO`;
- `TorsionFreeLiteratureInputsLeastArea.literatureInputs_of_leastAreaLeaves`;
- `TorsionFree.hullInputs_of_leastAreaLeaves` and `TorsionFree.hullTheorem71_of_leastAreaLeaves`;
- `HullSC.hullOneStepStatement_of_leastAreaLeaves` and `HullSC.hullCommonQuotient_of_leastAreaLeaves`;
- `GGT.RelHyp.fournierFacioQuotientStatement_of_leastAreaLeaves`.

| file | change | state |
|---|---|---|
| GGT/HullSCCommonQuotientCorrected | `hullCommonQuotient` is the `LiteratureInputs` field; names its least-area producer | landed 2e93f09d1 after probe 0913-025915-88905 GREEN (all seven BUILT) |
| GGT/HullSCLemma44Canonical | `hullLemma44CanonicalQuotientStatement_zero`: its consumer was retired and nothing uses it | same |
| GGT/HullSCLemma44JointRelabel | the re-spelling admission path is now described in the past tense | same |
| GGT/HullSCLemma49PowerDiagramFromComponents | "was the assembly leaf"; names the least-area twin statement | same |
| NonMF/FournierFacioParagraphFromSimpleFactor | the five literature-input bullets and the axioms note | same |
| NonMF/HullFillTheoremCCorrected | the printed forms are stated over `hullInputs_of_leastAreaLeaves` | same |
| NonMF/TorsionFreeSectionCitations | field table, residual paragraph, axioms note | same |
| NonMF/FFFParagraphFreeWitness | residual section and two theorem docstrings; the module has no importers | landed 12738313c after probe 0913-035649-36569 GREEN (BUILT; attic copy f6985a197) |
| scripts/TheoremCCompletionAudit.lean | "Superseded (2026-09-13)" header; every audit line kept | landed 9ac39c698 |
| scripts/check_non_mf_unconditional.py | taint-scan docstrings in the past tense | landed 9ac39c698 |
| metadata/MF_RECOGNITION_SENTENCE_MAP.tsv (row c6172bdc109a) and MF_RECOGNITION_SENTENCE_CENSUS.md:27 | seed-group note: E takes the three hypotheses; census line matches what the generator writes | landed 8f8b5ccab |

Files owned by other lanes were not edited. Their owners were messaged on 2026-09-13:
- hull-respell: GGT/HullSCOneStepQuasiGeodesicLeaves.lean:25-26, 38. hull-respell fixed it at 4dce22f1e, after probe 0913-070150-30707 BUILT;
- kh-ejz: Kazhdan/GHBLatticeRouteKazhdan.lean:68-69, and the kh-ejz census row ("TheoremC.kotowskiOllivier is still sorry").
  kh-ejz fixed both at 46f1c36a2, after probe 0913-034435-10433 GREEN;
- ko-closed: Kazhdan/KotowskiOllivierClosed.lean:11-12. ko-closed fixed it at 4be3a3a5c, after probe 0913-052526-4611 GREEN;
- nm-endpoints: TorsionFreeLeafAssembly.lean:29, 36-37, 123; TorsionFreeLiteratureInputsLeastArea.lean:18-23, 101;
  TorsionFreeSaturationFromCorrected.lean:21, 74, 264, 435.
  nm-endpoints fixed all three at fe61152ed, after probe 0913-030945-26927 GREEN.

All four owners have fixed their files, so no ask is still open.

Some hits were left unchanged:
- Accurate history: the TheoremCAssembly header, SeedFromTheoremC.lean:29-32, and theoremc-retire's row and report.
- Field names or unrelated declarations that share a name: RelHypFournierFacio:9, RelHypFournierFacioProp23:10,
  FournierFacioInput, TorsionFreeFourLeaves:158, GHBLatticeRouteKazhdan:23, and hull-respell's row.

## W1 (c) glue-back transport (2026-09-13)

Status 2026-09-13: go-lemma42 answered.  The lead gave sec2 one (c) module or instance, to be named by go-lemma42 and
written in a module sec2 owns.  go-lemma42 named two generic pieces that do not touch its files, and sec2 wrote both:

| module | carries | landed |
|---|---|---|
| GGT/VanKampen/OEquivalentCellFaces | `cellFaceEquiv`, `cellFaceEquiv_val`, `cellFaceEquiv_faceWord`, `OEquivalentDiscDiagram.faceEquiv`, `OEquivalentDiscDiagram.faceWord_faceEquiv`, `OEquivalentDiscDiagram.ofCellFaceEquiv`, `OEquivalentDiscDiagram.ofCellFaceEquiv_face` | a845f70a0, GREEN 0913-113305-58468 (base 945d97753, record md5 e32a0157 = main; replayed from the olean of 0913-101514-99667, where this module BUILT with no error) |
| GGT/VanKampen/Estimating/CyclicArcSub | `Embedded.CyclicArc.sub`, `sub_start`, `sub_length`, `sub_rotated`, `sub_darts` | a845f70a0, fix dc64bcdbb, GREEN 0913-102559-44269 (BUILT, bytes = main) |

Correction (2026-09-13 12:45): an earlier version of this table and wire-queue line 595 called 0913-101514-99667
GREEN.  That record reads PROBE FAILED rc=1.  Every error in it was in the co-probed CyclicArcSub, before the fix
dc64bcdbb.  root-wire held OEquivalentCellFaces for that reason.  sec2 re-probed it (0913-113305-58468 GREEN), marked lines
595-596 superseded, and queued a corrected entry at the end of the queue.  The module needed no change.

`cellFaceEquiv` matches the positions of the cell list with the relator faces.  So an O-equivalence is the same as a
word-preserving bijection of relator faces with the same boundary word.  `CyclicArc.sub arc i l h` is the arc of
length `l` starting `i` darts into `arc`, and its darts are `(arc.darts.drop i).take l`.  The consumers are
go-lemma42's Estimating/OsinPocketGlueDiagram (O-equivalence of X with the glued copy) and
Estimating/OsinPocketGlueTransport (target sub-arc on the outside cell).  go-lemma42 owns
`DiscDiagram.regionPiece_transport` and `OsinLoopCut.ofRegionPiece`.  The carrier is dgo-analytic's `PocketRegion`
(Estimating/OsinPocketRegion).

go-lemma42 has since landed the combinatorial glue (namespace `Surgery.PocketGlue`):

| module | carries | landed |
|---|---|---|
| GGT/VanKampen/SurgeryPocketGlue | `Seam`, `Seam.glueMap`, `Seam.glue_isRestriction` | 1e3497e4b, 0358f4537 |
| GGT/VanKampen/SurgeryPocketGlueCount | `glue_dartCount`, `glue_edgeCount`, `glue_faceCount` | 3af801bac |
| GGT/VanKampen/SurgeryPocketGlueVertices | `glue_vertexCount` | 0cdb0dc87 |
| GGT/VanKampen/SurgeryPocketGluePlanar | `glueMap_connected`, `glueMap_planar` | 291ae2c87 |

So the χ counts are done.  Still to come: Estimating/OsinPocketGlueDiagram, the diagram on `glueMap` through
`DiscDiagram.ofPlanar`, and Estimating/OsinPocketGlueTransport.  Of the lead's two examples, only the SectionPocketCut
instance (`cellTransport`, `sectionTransport`) is left.

Inputs `ofPlanar` needs on `glueMap`, as read.  M is Δ', the seam faces are `P.outside`, X is the O-equivalent copy,
and `outer` is its outer face:
- a label: M's label on `inl` and X's on `inr`.  `label_alpha` holds across the seam only if X's label on each `outer`
  dart equals M's label on the matching boundary dart;
- the outer face, the image of Δ'.outerFace (`outerFace_mem` puts it in `P.outside`);
- a `FaceBoundary` for every glued face, transported along `Seam.glueFaceEquiv`;
- `relFaces`, `hword` and `htriv`.

## Lemma 9.4 Case 2: carrying the optimum across the connector insertion (2026-09-13)

Status 2026-09-13 09:43: **done**.  The lead assigned sec2 to help sec5-sentences on CaseTwo of Lemma 9.4.  sec5 handed
over one sub-piece: carry the optimal section family across the connector insertion.  The steps after it are the merge
(`GFaceMerge.transportDistinguished`), the spike deletions and `DartMinimal.false_of_dartCount_lt`, and they belong to sec5.

| module | carries | state |
|---|---|---|
| Estimating/OsinLemma94InsertionTransport | `GloballyDistinguishedSectionFamily.insertionTransport` with `_diagram`, `_family`, `_card`, `_unboundSum`, `_dartCount_le`, `_avoid`, `_profile` | compiled: probe 0913-094211-23583 GREEN at base 0090d6edc, which contains the landing commit c652fa749 (md5 9fdb8cc7dfc51d96a8ecd722591ce8ef); every `#audit_axioms` gives propext, Classical.choice, Quot.sound; queued for wiring |

The inputs are:
- S, a globally distinguished section family;
- R : SplitCornerOutput (symmetricLabelAlphabet D) S.diagram f hf hcells start finish word;
- havoid : ∀ a ∈ S.family, f ∉ a.1.

Every field transports, so nothing was restated.  Write T for the transported family:
- `_diagram` and `_family` hold by rfl.  T.diagram = R.diagram, and T.family is the `regionFamily` of the original embedding.
- `_card` and `_unboundSum`: T has as many regions as S and the same unbound sum.
- `_dartCount_le`: T.diagram has at most S.diagram's dart count plus 2 * word.length.
- `_avoid`: no region of T contains R.prefixSide or R.suffixSide.
- `_profile`: every region of T has the `SameTargetProfile` of some region of S.

Helper lemmas in the same module:
- `DiscEmbeddingAway.unboundDarts_regionFamily`: the unbound darts of a transported cell are the old ones, through the dart
  embedding.  `sum_unboundDarts_regionFamily_card` sums this over the cells.
- `GFaceWordInsertion.SplitOutput.faceOf_retained_or_sides`: every face of a split insertion is a retained face, the prefix
  side or the suffix side.  These are F + 1 distinct faces, and the insertion has F + 1 faces.
- `mem_range_or_path` and `dartCount_le_add_two_mul`: so every dart is a retained dart, a dart of the path or the reverse of one.
- `RealizedSectionFamily.insertionSection` with `_weight`, `_card` and `_labelLegal`.

## Lemma 9.4 polygon realization: no two adjacent unselected G-faces (2026-09-13)

Status 2026-09-13: **already on main, no module written**.  The lead assigned sec2 the first piece of hull-unbound's
PolygonRealization split.  The claim is that in a globally distinguished, dart-minimal family no edge has two different
unselected G-faces on its sides.  hull-unbound had already proved it in Estimating/OsinLemma94PolygonRealization
(1130c8dbc, queued for wiring):
- `GloballyDistinguishedSectionFamily.GFacesApart S`: for every dart d, if the faces of d and of `alpha d` are both
  `UnselectedGFace`, then they are equal;
- `gFacesApart_of_dartMinimal (hS : S.DartMinimal) : S.GFacesApart`.  Its proof merges across the edge with
  `Surgery.GFaceMerge.transportDistinguished` and then uses `transportDistinguished_sum_unboundDarts_card` and
  `transportDistinguished_dartCount_add_two`.

As the lead's fallback says, sec2 asked hull-unbound for the face-partition piece (`OsinLemma94PolygonPartitionInput`) or
another unassigned sub-piece.  ROSTER gives the partition to ghw-assembly, so sec2 also asked ghw-assembly for an
unassigned sub-piece.  As of 12:45 neither lane had named one, and sec2 told the lead so.  Since then ghw-assembly has
closed the partition (`osinLemma94PolygonPartitionInput`, Estimating/OsinLemma94PolygonPartition, 746028b24, with
`#audit_closed_axioms`), so no sub-piece is free.

## Lemma 9.4 Case 2: the separated corner insertion (2026-09-13)

Status 2026-09-13 13:10: **done**.  sec5-sentences stated the Prop
`GloballyDistinguishedSectionFamily.SeparatedCornerInsertionInput` (Estimating/OsinLemma94SeparatedInsertion, b52230097).
Its consumer is sec5's `osinLemma94CaseTwo_of_insertion`, and sec5 handed the proof to sec2.  sec5 has since landed
`osinLemma94CaseTwoInput` (Estimating/OsinLemma94CaseTwo, e0e94015d, with `#audit_closed_axioms`).  It consumes this
proof, so Case 2 of Lemma 9.4 is closed.

| module | carries | state |
|---|---|---|
| Estimating/OsinLemma94SeparatedInsertionProof | `separatedCornerInsertionInput : SeparatedCornerInsertionInput.{u, w, v}`, `#audit_closed_axioms` | compiled: probe 0913-130436-67131 GREEN (BUILT) at base 5a716fd85, which contains the landing commit 619b70139 (md5 3432a9fa904b60987e83537804841c8f = main); `#audit_closed_axioms` gives propext, Classical.choice, Quot.sound; queued for wiring |

Proof.  The walk of f from base r reads `front ++ back`, and n is its length.
- start := r % n, and finish is the corner `front.length` darts later (`CornerInsertion.exists_forwardOffset_eq`).
- `GFaceWordInsertion.exists_split_corner_output` gives R, and T := `insertionTransport S R`.  The counts come from
  `insertionTransport_unboundSum` and `SplitOutput.dartCount_eq`.
- path' := path.map R.embedding.darts, first := R.suffixSide and second := R.prefixSide.  The suffix side reads the new path
  and then `back`.  The prefix side reads the reversed new path and then `front`.
- Joints, along `path`: `back` contains `path` from offset |s|, so the suffix-side chain gives facePerm e = e'.
- Joints, across `path`: let alpha x' sit at position p of `front`.  The old walk sends it to alpha x at position p + 1.  If
  p + 1 = |front|, then alpha x would be the first dart of `back` and also lie in `front`, against `nodup_append`.  So the
  prefix-side chain gives the step.
- Unselected sides: `SplitOutput.side_ne_outerFace`, `side_ne_cellFace` and `insertionTransport_avoid`.

The module imports simple-group's Estimating/OsinLemma94CornerInsertion (f7538e223, queue line 623) and uses its helpers
(`CornerInsertion.rel_of_getElem?`, `getElem?_map_of_getElem?`, `exists_forwardOffset_eq`, the `SplitOutput` face lemmas)
rather than copying them.

Construction constraint for the partition, from reading the fields.  Suppose only one section is nonempty and a walk runs
along the boundary through position 0 of `outerDarts` at a vertex of degree two, so `facePerm (alpha e') = alpha e` for
e = alpha o_0 and e' = alpha o_(m-1).  `boundary_arc` forbids arcs that wrap around, so the walk must split between e and e',
and both halves have the same kind.  `Maximal` checks only the pairs with `i + 1 < sideCount`, so `base k` must be placed
at this split.  The split happens at most once per walk.

ghw-assembly reports that the closed partition handles this split by where the walk starts.  The three declarations
below are on main; sec2 has not read their proofs.
- When the head of `outerDarts` lies on the face walk, `baseOf f` starts the walk there (`head?_rotate_baseOf`,
  Estimating/OsinLemma94PolygonSides, a76186267).
- `SameSide` on boundary darts requires `outerPos e' = outerPos e + 1`.  So the split between `alpha o_0` and
  `alpha o_(m-1)` is a break: the pair (last side, side 0), which `Maximal` never checks.
- In `sidesBreak_of_groups` (Estimating/OsinLemma94PolygonMaximal, 9f03bfcd3), `head?_flatten_ne_of_lt` excludes, at
  index i+1 ≥ 1, a junction whose `e'` is that head.

## Pocket kept cell on the O-equivalent copy (2026-09-13)

Status 2026-09-13, after 3e7ce7227: **partial**.  There is no avoidance binder.  Simple walks take `hw`; noncrossing
walks take `hw` and `hfollows` (hull-select).  The lead's item is kh-ejz's residual
(ii): the premise `hkept : (cell X' kept).face ∈ sideFaces X'.toCombMap K.walk` of `PocketWalk.toPocketFaceSet`, on the
copy `X'`.

Transport.  `OEquivalentDiscDiagram` keeps `boundaryWord`, `cellIndex` and `cellWord` but no darts.  So it cannot carry
the side of a walk, and hull-select's `zeroCellPocketMerge` cannot be transported along it.  A transport is not needed
either.  hs-vanishes' `OuterSpurThickeningStatement` gives a globally distinguished family `S'` whose diagram is
O-equivalent to `S.diagram`.  The equivalence of the two families keeps the weight, the target profile and the source
index.  So `X' = S'.diagram`, and the kept cell is a theorem on a family's own diagram.  hull-select's files are
untouched; the new module only imports OsinPocketZeroCellMergeFalse.

| module | carries | state |
|---|---|---|
| Estimating/OsinPocketKeptCell | `RealizedSectionFamily.targetArc_end_le_start`; `GloballyDistinguishedSectionFamily.exists_kept_of_pocketRegion` and `exists_kept_of_simple`; `#audit_axioms` on all three | compiled: probe 0913-140023-67387 GREEN (BUILT) at base 492057fb6, the landing commit (md5 4d34649d91379d23a7b79a4b2966eff3 = main); unwired, queued for wiring |
| Estimating/OsinPocketKeptCellAbsorbed | `Embedded.FaceSetBoundary.subset_or_disjoint`; `RealizedRegionFamily.subset_of_not_disjoint_pocketRegion`; `PocketMeetsContainedStatement` with `pocketMeetsContained` (`#audit_closed_axioms`); `GloballyDistinguishedSectionFamily.false_of_disc_absorbed_section`, `exists_kept_of_pocketRegion_of_value`, `exists_kept_of_simple_of_value` (`#audit_axioms`) | compiled: probe 0913-150844-93030 GREEN (BUILT) at base 53ef29c55, which contains the landing 3a76a2fb8 (md5 2696aec84213d40e089928383a4106ed = main); unwired, queued for wiring |
| Estimating/OsinPocketKeptCellNoncrossing | `PocketWalk.outerFace_not_mem_sideFaces_of_noncrossing`, `GloballyDistinguishedSectionFamily.exists_kept_of_noncrossing_of_value` (`#audit_axioms`); `PocketKeptCellNoncrossingStatement` with `pocketKeptCellNoncrossing` (`#audit_closed_axioms`) | compiled: probe 0913-155924-73125 GREEN (BUILT) at base 58aef0a2b, which contains the landing 3e7ce7227 (md5 7aaf15704e7b4c6919f9b22f80a4c45a = main); unwired, queued for wiring |

`exists_kept_of_simple` takes the output of `PocketWalk.exists_of_exteriorAt` on `S` (regions `x ≠ y` exterior to cell
`i` and targeting section `j`, the walk `K`, the gap equation, the two target-arc endpoints), and then:
```lean
    (hw : IsSimpleClosedWalk S.diagram.toCombMap K.walk)
    (havoid : ∀ z ∈ S.family, z ≠ x → z ≠ y → Disjoint z.1 (sideFaces S.diagram.toCombMap K.walk)) :
    ∃ kept : Fin S.diagram.rCellCount, (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk
```

Proof.
- Suppose no relator cell lies on the side.
  - Then the side is a relator-free pocket region (`PocketRegion.ofSimpleClosedWalk`).
  - A target-arc dart is a walk dart on the outer cycle, so the exterior face is outside
    (`outerFace_not_mem_sideFaces_of_mem_outerDarts`).
- Rotating `K.walk` by the length of the first side gives the decomposition of `mergedGeometry`, with no target cell.
- Weight.
  - The gap equation splits the source arc.
  - The target arc of `x` ends before that of `y` starts (`targetArc_end_le_start`), since a dart in both would lie in
    two disjoint face sets.
  - So `x.weight + y.weight ≤ |K.src| + |K.tgt|`, and `false_of_disc_pair_singleton` gives False.
- The order of the two target arcs is derived, not assumed.  If the target arc of `y` started first, it would end before
  that of `x` starts, and `hend` would make `K.targetArc` empty.

Open.
1. **Noncrossing walks.**
   - `toPocketFaceSetOfNoncrossing` needs `hkept` for a noncrossing walk, which is the case that covers a pinch.
   - `PocketRegion` asks for `IsDiscRegion` on both sides.  A pinched cycle fails `FollowsBoundary`
     (`OsinPocketPinchedTwoGonModel.not_followsBoundary`), so the walk's side cannot come from
     `toDiscRegion_of_followsBoundary`.
   - The producer is dgo-analytic's `PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler`
     (Estimating/OsinPocketRegionNoncrossingWalk, 8bbf0a9c8, wired).  Its `inner.cycle = walk` holds by `rfl`.
   - **Blocker 1** was its premises `hout`, `hfollows` and `heuler`.  Module `Estimating/OsinPocketKeptCellNoncrossing`
     (table above) removes two of them.
     - `hout` is proved: a target-arc dart is a walk dart whose reversal lies on the exterior face
       (`PocketWalk.outerFace_not_mem_sideFaces_of_noncrossing`).
     - `heuler` is `hw.reclosed_euler S.diagram.planar hfollows` (hull-euler, NoncrossingClosedWalkEuler at 19866c7d6,
       GREEN record 0913-150114-7274, bytes = main).
     - `exists_kept_of_noncrossing_of_value` keeps two hypotheses, `hw : IsNoncrossingClosedWalk S.diagram.toCombMap
       K.walk` and `hfollows : (hw.outerCycle S.diagram.planar).FollowsBoundary`.  hull-select produces both from
       first turns (`firstTurnWalkPocketInputs`, Estimating/OsinPocketFirstTurnWalk).
     - The conclusion is the `hkept` premise of `PocketWalk.toPocketFaceSetOfNoncrossing`.
   - **Lead item 16:20: the FirstTurn chain for `K.walk`, to drop `hw` and `hfollows`.  Blocked (reported to main and
     hull-select); no module written.**
     - The shape is forced.  `exists_kept_of_pocketRegion_of_value` takes `hinner : P.inner.cycle = K.walk`, so
       `firstTurnWalkPocketInputs` applies to `c = invDarts K.walk = inv t_2 ++ inv x.rightSide ++ K.sourceArc.darts ++
       inv y.leftSide`, and `K.walk = c.reverse.map alpha`.
     - Every joint of `K.walk` is of one of two kinds (from `boundary_decomposition`, `cycle_chain`, `FaceBoundary.chain` and
       the equations of `exists_of_exteriorAt`).
       - (i) A `BoundaryStep` of `x` or `y`: the joints inside the two sides and the four corners.  The inner sector at the
         vertex consists of internal darts of the region.
       - (ii) A face step of the source cell or of the exterior face: the joints inside `t_1` and `t_2`.  The outer sector
         is a single corner.
     - `FirstTurn` on `c` asks that the outer sector hold no kept dart.  So the (ii) joints are `FirstTurn.of_facePerm`,
       and the (i) joints are not controlled.
     - Obstruction, the lake.  Let `d → e` in `x.rightSide` and `d' → e'` in `y.leftSide` pass through one vertex `v`.
       - The inner sectors are disjoint, since the regions are.  So `alpha d'` and `e'` lie in the outer sector of `x` at `v`.
       - The first turn from `alpha e` reaches `alpha d'`, a dart of `c`, before `alpha d`.  So `FirstTurn` fails.  The
         complement's `BoundaryStep` stops at the same dart, so `hfollows` fails for `K.walk` too.
       - If the sides share an edge, `alpha_not_mem` fails, so `hw` fails as well.
       - Nothing in `exists_of_exteriorAt` or the family fields rules out the touch.  They only make the regions
         face-disjoint.
       - This is Configuration B of `Estimating/OsinPocketLakeModel.lean`: the source cell lies in the lake, and `K.faces`
         is an annulus pinched at `v`.  `Estimating/OsinPocketFirstTurnWalkModel.lean` (l.17-20) already records that the
         first-turn hypotheses exclude the lake.
     - What survives the lake.  These are hand arguments, not Lean.
       - Passages at a vertex do not interleave.
         - Strictly inside the inner sector of a (i) joint lie only internal darts of the region.  No walk dart is
           internal, and neither is the reversal of one.
         - Strictly inside the outer sector of a (ii) joint there is nothing.
         - So `hw` holds when the sides meet only at vertices.
       - Both reclosings keep χ.
         - In the two-petal lake, reclosing the complement gives `sigma' = (0 3)(1 2)`, so V = 2, E = 2 and F = 2.  The
           merge splits the pinch vertex.
         - So `P.outer` is a disc region, but no producer builds it: `toDiscRegion_of_followsBoundary` needs `hfollows`.
       - `hw` alone does not give χ.  The three-petal rose (`NoncrossingClosedWalkEuler.lean` l.22-24,
         `SurgeryNoncrossingCollarStripModels.lean`) is noncrossing, and reclosing its side gives a torus.  Its passages
         interleave.
     - The endpoint needs `P.outer`.  `InnerDiscRegion.ofPocketRegion` takes `value_one` from `P.listVal_inner_eq_one`.
       That lemma reads the boundary value of `P.diagram` (`OsinPocketRegion.lean:158`, `replaceGRegion … P.outside
       P.outer`).
     - Options put to the lead:
       - (i) a producer that the sides of distinct regions share no vertex (a new surgery);
       - (ii) another pocket;
       - (iii) keep `hw` and `hfollows` as in 3e7ce7227;
       - (iv) an Euler producer, without `FollowsBoundary`, for both reclosings of a noncrossing walk whose passages do
         not interleave.  hull-euler owns `NoncrossingClosedWalkEuler`.  sec2-sentences would prove non-interleaving
         for `K.walk` from the two joint kinds.  A shared edge still needs (i) or (ii).
2. **`havoid`: removed by absorption (2026-09-13 15:10).**  Module `Estimating/OsinPocketKeptCellAbsorbed` (table
   above).
   - Notation: `t_1 = invDarts S.diagram K.sourceArc.darts` and `t_2 = K.targetArc.darts`, the source and target parts
     of `K.walk`.
   - A third member of the family can lie inside the pocket, so `havoid` was a real premise.  The new theorems drop it,
     and with it `hstart`, `hend`, `hjx` and `hjy`.
   - New premises: `hfirst : K.firstSide = y.2.leftSide`, `hsecond : K.secondSide = x.2.rightSide` and
     `hvalue : ∀ C ∈ S.diagram.relatorCells, RelLetter.listVal C.word ≠ 1`.
     - `PocketWalk.exists_of_exteriorAt` gives `hfirst`, `hsecond` and the gap equation.
     - `S.cell_listVal_ne_one hW hlambda hrho` gives `hvalue`.
   - **Meets implies contained**: the named Prop `PocketMeetsContainedStatement`, proved by `pocketMeetsContained`.
     - Statement: for a pocket region `P` whose cycle is the walk, every selected region meeting `P` lies in `P`.
     - Proof: a region dart leaving `P` lies on the walk.
       - On a side it lies on the boundary of `y` or `x`, which contradicts disjointness.
       - On `t_1` it crosses into the cell `i`, whose word has value `≠ 1`.
       - On `t_2` it crosses into the exterior.
     - `Embedded.FaceSetBoundary.subset_or_disjoint` then gives containment.
   - Model tests, before building.
     - (a) Two lobes touching at a walk vertex are excluded by the region's own `FaceSetBoundary`.
       - Membership in `P` is constant along boundary steps, so an edge-disconnected second part has no boundary dart.
       - That part is then closed under `alpha` and `sigma`, and by planarity it holds the exterior face.  This
         contradicts `all_gCells`.
       - Smallest model: `OsinPocketPinchedTwoGonModel.no_faceSetBoundary`.
     - (b) The face of cell `i` needs `hvalue`.  With it, neither model breaks the Prop.
   - Weight.
     - The collapse absorbs `A = {a ∈ S.family | ¬ Disjoint a.1 P.faces}`, which holds `x` and `y`: the source darts of
       each lie on `t_1`.
     - The source and target darts of the members of `A` are pairwise distinct.  Each leaves `P` into a relator cell
       or the exterior, so it lies on `t_1 ∪ t_2`.  A side is excluded by disjointness, or by `cycle_nodup` for
       `x` and `y` themselves.
     - So `familyWeight A ≤ |t_1| + |t_2|`, and `false_of_disc_collapse_singleton` gives False.
   - Separate route: debt-conditional is writing a two-gon `havoid` (face-class invariant,
     `Estimating/OsinAppendixEulerTwoGonPocketClass`).

## Census

Rows: `metadata/nm-census-rows/sec2-sentences.tsv`.  The four sentences with no declarations
(6a52924d8260, db7009c5a941, 2a0e1987e5c2, a1f7e96658eb) are setup or motivation and are graded structural.

## Traps found

- `map_sub`/`map_mul`/`map_zero` on `normMatrixCStarCoronaMk` time out in instance search; `RingHom.map_*` compiles.
- `map_continuous` on `→⋆ₐ[ℂ]` into a norm matrix corona finds no ContinuousMapClass even under
  `open scoped CStarAlgebra`; `LinearMap.mkContinuous` with `NonUnitalStarAlgHom.norm_apply_le` compiles.
- `•` on `BoundedMatrixSequence (fun n ↦ cornerModel …)` times out; Nonempty binders plus type ascriptions fix it.
- After `rw [comapHom_b, wallAction_b]` the norm is still taken at the carrier `(A.comapHom ρ).E`, so `rw [norm_smul]` finds
  no occurrence.  Prove the identity in `Lp ℝ 2 shellMeasure` and close with `exact`.
- `push_neg` is deprecated at the pin, and warningAsError makes it an error; use `push Not at h`.
- `#audit_closed_axioms` rejects any theorem whose type starts with a binder: wrap endpoints as named Props.
- `nmprobe.sh` refuses the whole probe if `$NM/lanes/<lane>.files` holds any path that is not `GroupApproximation/**/*.lean`.
  Keep scripts and metadata out of that file; nmland does not check them against a green record.
- `metadata/MF_RECOGNITION_SENTENCE_CENSUS.md` says "Do not edit", but CI regenerates it with `--check`.
  A note change in the map must also be made in the matching md line, exactly as `scripts/sentence_census.py` writes it (`  * {note}`).
- `CornerOutput.originalReplacement`, `originalEmbedding` and `originalCellMap` already start from the original diagram.
  Adding a `GFaceRebase.replacement` step in front gives an application type mismatch (probe 0913-093536-9874).
