# Lane ms-traces-2: tex 1856–1976 (prop:locally-rf-by-z-trace, the construction of W, eq:affine-clifford-witness)

Lead: session nonsofic-existence-49 (wave 2, ROSTER-wave2 Brief R). Snapshot: origin/main 5b3910136 (tex 2507 lines).

## Ledger

All 29 census rows of the range were matched by text against the current tex. None drifted: the census is keyed at
the pre-chain-core hash, but these sentences did not change. Every sentence of tex 1856–1975 has a row. Carriers are
root-imported and audited in `Manuscript/NonMF/Audit/Sec4.lean`. `#audit_axioms` throws on non-classical axioms and
`#audit_closed_axioms` also refuses leading binders. The Analysis chain of the proposition has no Prop binder standing
for a cited result.

| key | tex | status | carrier | verdict |
|---|---|---|---|---|
| a817c6ae86c9 | 1856–1857 | definition | `LocallyRFByIntAmenableTrace.IsLocallyResiduallyFinite` | PASS; the row is ms-traces-1's (range 1808–1858), which also graded it PASS |
| fd8372f71c2d | 1861–1862 | formalized | `AmenableExtensionTrace.manuscriptPrintedAmenableExtensionTrace` | PASS: closed endpoint. A normal `N ≤ G`, `G` countable, `G ⧸ N` amenable (`Nonempty InvariantMean`) is the printed extension up to isomorphism |
| 0bd25ebcbeac | 1862–1864 | formalized | same | PASS: `IsQuasidiagonalTrace τ_N ∧ IsAmenableTrace τ_G` |
| d47b613bb096 | 1869–1872 | structural | overview | PASS |
| a97f0ab46cd9 | 1873–1875 | formalized | `AmenableExtensionSentences.manuscriptSentence_cocycleValues` | PASS |
| 94ebd1377c15 | 1876–1879 | formalized | same | PASS (`b = esCocycleN`, `σ = sect`) |
| 6e563dbca22b | 1880–1883 | formalized | `manuscriptSentence_cocyclePacketSeparates` | PASS |
| 30eb3e57ac10 | 1884–1888 | formalized | `manuscriptSentence_cosetsDistinct`, `..._compressionUCPAndTranslation` | PASS |
| da2fd300384a | 1888–1892 | formalized | `manuscriptSentence_compressionUCPAndTranslation` | GAP G5: the carrier gives `g • σ(x)r_qΛ ∈ T`, not the printed formula `gσ(x)r_qΛ = σ(ḡx)r_{θ(b(g,x))q}Λ` |
| 89bc31ec5034 | 1893–1900 | formalized | `manuscriptSentence_rankBoundGivesHS` | GAP G3: the printed identity `Φ(u_gh)−Φ(u_g)Φ(u_h) = Πλ(g)(1−Π)λ(h)Π` and the printed display `‖·‖₂² ≤ \|{x∈F : h̄x∉F}\|/\|F\|` are not stated; the carrier bounds by `√(1/(n+1))` |
| 1ea7f92c66a1 | 1901–1905 | formalized | `manuscriptSentence_traceIsFixedPointFraction` | GAP G2: "trace = fraction of fixed points of T" is not stated for general g, and the two printed cases (ḡ≠1 moves the F-coordinate; ḡ=1 gives θ(b(g,x))q≠q) are replaced by a one-step argument (see the docstring of `AmenableExtensionAmenableTrace`) |
| b77ceccea9ed | 1906–1911 | formalized | `manuscriptSentence_folnerLimitsExtend` | PASS |
| 23d58dbda4bf | 1913–1917 | formalized | `manuscriptSentence_stage*` | PASS |
| 8e53d32e3fb8 | 1920–1923 | structural | `AmenableTraceSentencesB.manuscriptSentence_defectFactorization`, `CliffordWitnessDirectDefect.signSubgroup_le_printedDefect` | GAP G4: the sentence asserts that 𝔇_W(Γ) contains a commutator whose square is a central involution. The pieces exist (`pointDefect = ⁅x, ι a⁆`, `pointDefect_mem_printedDefect`, `sign_eq_pointDefect_sq`, `signAmbient_central/_sq/_ne_one`), but no declaration states the sentence, so the row is graded `structural` while it asserts mathematics |
| 60898a519f4f | 1923–1926 | definition | `CliffordWitnessDirectDefect.PrintedCliffordWitnessNotIsOperatorMF` | PASS (countable Γ with (T), injective α, a ∉ range α) |
| c180c0186454 | 1926–1932 | definition | `MappingTelescope.Telescope`, `MarkedCompression.Vertical` | PASS (`V = T_α ⋊[shift] ℤ`) |
| d5c52ca23af0 | 1933–1935 | formalized | `CliffordConstructionSentences.manuscriptSentence_hnnExtension` | GAP G1: the carrier gives `tι(g)t⁻¹ = ι(αg)` and that every element of T_α sits at some level. Missing: (a) "V is the ascending HNN extension of Γ along α", i.e. `V ≃* HNNExtension Γ ⊤ α.range` with `t ↦ t`, `ι ↦ of` (`MarkedCompressionGroup`'s docstring asserts this without proof); (b) `T_α = ⋃_{n≥0} t^{-n}Γt^n` inside V (`inl_level_succ` is the step, not the union) |
| 08844a3bdb91 | 1936 | definition | `MarkedCompression.Cosets`, `rootCoset` | PASS |
| 86ba78fb0d96 | 1936–1942 | formalized | `manuscriptSentence_cliffordLampPresentation` | PASS: `CliffordLamp X := PresentedGroup (relators X)` |
| 4cbf47e489a6 | 1943–1945 | structural | `CliffordLamp.crossing` | PASS: `crossing f g = Σ_x Σ_{y<x} f x * g y`, the printed `B(f,g) = Σ_{x>y} f(x)g(y)` |
| dc43ec6b23ed | 1945–1948 | formalized | `manuscriptSentence_signedModelGroupLaw` | PASS; the row should also name `CliffordLamp.crossing_add_left/_right` (the printed "since B is bilinear") |
| 4704b74b6c8e | 1949–1952 | formalized | same | PASS |
| 1fab0dcc8e88 | 1953–1954 | formalized | `manuscriptSentence_toModelHomomorphism` | PASS |
| b9ca7188b1f5 | 1954–1959 | formalized | `manuscriptSentence_cliffordLampNormalForm` | PASS: `section' ⟨a, f⟩ = signPow a * wordOfSupport f.support`, and `wordOfSupport s = wordOfList (s.sort (· ≤ ·))` (CliffordLampNormalFormSplice:126) is the printed `ε^a c_{x₁}⋯c_{x_r}` with `x₁ < ⋯ < x_r` |
| 407925e64c6c | 1960–1961 | formalized | same | PASS |
| 51284d178433 | 1962–1964 | formalized | `manuscriptSentence_cliffordLampCountableLocallyFinite` | PASS |
| c41bad22d29b | 1964–1968 | formalized | `manuscriptSentence_cliffordLampKillSignCentralExtension`, `..._wCentralExtensionOfWreath` | PASS |
| ad753104ce33 | 1968–1971 | formalized | `manuscriptSentence_permutationAutomorphism` | PASS (`permHom : Equiv.Perm X →* MulAut (CliffordLamp X)`) |
| 5306701b688c | 1971–1975 | formalized | `manuscriptSentence_verticalActsOnLamp` | PASS (`lampAction : Vertical →* MulAut`; `Ambient` = lamps ⋊ Vertical) |

## Gaps and plan

G1–G5 get new carrier modules. Ownership check done 17:0x: no lane `.files` lists these carriers; the paths are free on
disk and on origin; the adjacent lanes are ms-traces-1 (tex 1808–1858) and ms-traces-3 (1977–2106).

- CLAIM G4 `GroupApproximation/Manuscript/NonMFSentences/CliffordDefectCommutatorSentence.lean`: the sentence at tex
  1920–1923 (𝔇_W(Γ) contains the commutator `d = [tct⁻¹, a]` with `d²` a central involution; `⟨ε⟩` is a finite central
  subgroup inside 𝔇_W(Γ)).
- CLAIM G2, G3, G5 `GroupApproximation/Analysis/AmenableExtensionPrintedSteps.lean`: the printed translation formula,
  the coordinate form of `Φ(u_gh)−Φ(u_g)Φ(u_h) = Πλ(g)(1−Π)λ(h)Π`, the printed display
  `‖·‖₂² ≤ |{x∈F : h̄x∉F}|/|F|`, the trace as the fixed-point ratio, and the two printed cases.
- CLAIM G1 `GroupApproximation/Sofic/VerticalAscendingHNN.lean`: `V ≃* HNNExtension Γ ⊤ α.range` (`t ↦ t`, `ι ↦ of`) and
  `T_α = ⋃_{n≥0} t^{-n}Γt^n` inside V.

## Item 2 (main ~18:45): binder 3's island case, helping ms-intro-1

Context: a Case 1 X-walk `X₁ t X₂ t⁻¹ X₃` runs through a cutting path t around an island that holds a relator cell. The
pocket side is disconnected across t, so it is not a PocketRegion, and the walk is not simple. Main's ruling: ms-intro-1
lands `OsinLemma94CaseOneIslandStatement`; the loop cut comes from the enclosed singular subdiagram of the closed walk,
Osin's Γ joined along t. I proposed the split to ms-intro-1 in one direct message (~18:50): ms-intro-1 owns the island
statement, its reduction and the audit of `ofPlanar`, `isRelatorProduct_of_planar`, `InnerDiscRegion` and the zero-cell
merge; this lane owns A–C below.

- CLAIM A `GroupApproximation/GGT/VanKampen/ClosedWalkEnclosedSubdiagram.lean`: `EnclosedFaceSet`,
  `ClosedWalkEnclosedSubdiagramStatement` (Ξ reads the walk, carries the enclosed relator cells, least area inherited) and
  `enclosedSubdiagram_leastAreaCut`.
- CLAIM B `GroupApproximation/GGT/VanKampen/Estimating/OsinEnclosedSubdiagramLoopCut.lean`:
  `OsinLoopCut.ofEnclosedSubdiagram`, `EnclosedSubdiagramLoopCutStatement` and `EnclosedCellTransportStatement`.
- CLAIM C `GroupApproximation/GGT/VanKampen/ClosedWalkIslandModel.lean`: a closed island model (not simple; enclosed and
  disconnected across t; calibration of Ξ).

Ownership check (~18:50): the paths and names are free on origin, in the shared tree and in every `lanes/*.files`.

## Progress log

- 17:16: ledger landed (677b7cf09).
- 17:17: probe 0913-171711-24588 GREEN. All three modules BUILT and COMPILED, with `#audit_closed_axioms` and `#audit_axioms`
  in each module. The lead restart killed the local waiter, so no record was written. The re-probe 0913-172928-65828 was
  GREEN, restoring the same md5s from the cache, and wrote the record. Attic copies f9af58705.
- 17:3x: **G1–G5 CLOSED, LANDED b593627ca** (wire queued: AmenableExtensionPrintedSteps, CliffordDefectCommutatorSentence,
  VerticalAscendingHNN).
  - G1 `VerticalAscendingHNN.verticalEquivHNN : Vertical α hα ≃* HNNExtension Γ ⊤ α.range (ascendingIso α hα)`, sending
    `t ↦ t` and `ι γ ↦ of γ`; closed endpoint `manuscriptPrintedVerticalIsAscendingHNN`; plus
    `manuscriptSentence_telescopeIsUnionOfConjugates`: `range inl = ⋃ₙ {t⁻ⁿ ι(γ) tⁿ}`.
  - G2 `AmenableExtensionPrintedSteps.manuscriptSentence_traceIsFixedPointRatio`, `..._traceCaseMovesFolnerCoordinate`
    (ḡ ≠ 1) and `..._traceCaseFibre` (ḡ = 1: `b(g,x) = σ(x)⁻¹gσ(x) ≠ 1` and `θ(b(g,x))q ≠ q`).
  - G3 `..._defectIsBoundaryCompression` (the entrywise identity) and `..._printedHSDisplay`
    (`‖·‖₂² ≤ |boundary F h̄| / |F|`).
  - G4 `CliffordDefectCommutatorSentence.manuscriptSentence_defectContainsCommutatorSquaringToCentralInvolution` and
    `..._finiteCentralSubgroupInDefect`.
  - G5 `AmenableExtensionPrintedSteps.manuscriptSentence_translationFormula`.
  - Census rows landed with this report: `metadata/nm-census-rows/ms-traces-2.tsv` (8e53d32e3fb8 regraded from structural
    to formalized; d5c52ca23af0, da2fd300384a, 89bc31ec5034 and 1ea7f92c66a1 gain the new carriers; dc43ec6b23ed and
    5306701b688c name existing carriers they omitted).
- Range state: every sentence of tex 1859–1976 is carried by a closed declaration along the printed route, or is honestly
  `structural` (d47b613bb096, 4cbf47e489a6) or a `definition`. The new carriers become root-reachable once root-wire
  wires b593627ca.
- 19:15 (item 2): A, B and C written; claim landed 6017fd1a7, attic copies 782b0019f; probe 0913-191818-69417 running.
  - A `ClosedWalkEnclosedSubdiagram`: `EnclosedFaceSet Δ faces outerWalk` (the outside walk lists the reverses of the
    boundary darts of `faces` plus bridge darts both ways; closed dart walk; the turning condition of
    `IsNoncrossingClosedWalk` without `alpha_not_mem`); `ClosedWalkEnclosedSubdiagramStatement` (∃ Ξ reading
    `invDarts outerWalk`, at most the enclosed cells, a cell when the set holds one, a word-preserving index
    embedding, least area inherited); `enclosedSubdiagram_leastAreaCut`.
  - B `Estimating/OsinEnclosedSubdiagramLoopCut`: `EnclosedSubdiagramLoopCutStatement`, the hypotheses of
    `nonempty_osinLoopCut_of_pocketRegion` over an enclosed face set. It is the Prop ms-intro-1's
    `OsinLemma94CaseOneIslandStatement` reduction consumes.
  - C `ClosedWalkIslandModel`: six darts, relator loops Π and I, bridge t. The pocket walk `[2,4,3,0]` is a closed dart
    walk and not simple; `{Π, I}` shares no edge; `EnclosedFaceSet diagram {Π, I} [1,2,5,3]`; calibration: the clauses
    of the construction statement hold, realized by the diagram itself.
- 19:20: ms-intro-1's audit. `DiscDiagram.ofPlanar` (+ `ofPlanar_boundaryWord`, `ofPlanar_rCellCount`),
  `exists_relatorCells_of_planar` and the proofs of `PocketRegion.diagram_rCellCount_pos` and `_lt` supply Ξ and its
  counts over a planar map along the walk. w1-binder-2 is building that map (`BridgeComponentMap`, the far component of
  an edge deletion). The missing piece is least area: `length_filter_mem_le` needs `IsDiscRegion`. Named in A as
  `EnclosedLeastAreaFilterStatement`, with `leastArea_of_enclosedLeastAreaFilter` giving the least-area clause from it.
  `InnerDiscRegion` and the zero-cell merge do not apply (they need disc regions or FollowsBoundary).
