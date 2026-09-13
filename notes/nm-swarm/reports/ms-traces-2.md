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
| a817c6ae86c9 | 1856–1857 | definition | `LocallyRFByIntAmenableTrace.IsLocallyResiduallyFinite` | PASS |
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
| b9ca7188b1f5 | 1954–1959 | formalized | `manuscriptSentence_cliffordLampNormalForm` | pending: `section'` is the printed ordered word |
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

## Progress log

- 17:0x: ledger landed.
