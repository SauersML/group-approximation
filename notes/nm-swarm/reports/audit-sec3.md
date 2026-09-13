# audit-sec3 lane report

Lane `audit-sec3` audits tex 785–1620 of `non_mf_groups_exist.tex`: Section
`sec:one-sided-inverses` (tex 785–1323) and Section `sec:amenable-nonqd` (tex 1324–1620).

## Landed

- `3ae281ab9`: the first version of `GroupApproximation/Manuscript/NonMF/Audit/Sec3.lean`, the
  permanent gate for tex 785–1323. No green probe built it. The probe that named it,
  `0913-025304-66495`, failed (rc=1).
  - The wire queue's 03:13 entry for it wrongly said GREEN and is withdrawn.
  - `80abe6604` supersedes it.
- `b9772f360`: probe GREEN (tag `0913-030424-12674`, BUILT both modules), bytes identical to
  main, both wired:
  - `GroupApproximation/Manuscript/NonMF/Audit/Sec4.lean`, the permanent gate for tex 1324–1620.
  - `GroupApproximation/Manuscript/NonMF/AffineDoublingLiteralModel.lean`, the carrier of defect 2
    below.
- The landing that carries this report: probe GREEN (tag `0913-040726-62527`, BUILT `Audit.Sec3`; the carrier's bytes are
  those BUILT at `0913-035646-36298`). Both
  modules are on the wire queue, carrier first:
  - `GroupApproximation/Manuscript/NonMF/RingCompressionCellGeneral.lean`, the carrier of defect 1
    below.
  - `Audit/Sec3.lean`, regenerated from the census at origin/main `42d443298`, with the new
    carrier and the rows the jacobson and leavitt-units lanes have filled since.
  - The row corrections `metadata/nm-census-rows/audit-sec3.tsv`.

## The rows in range

The census has 254 rows in range: 202 formalized, 26 definition, 17 structural, 6 partial and
3 attribution.

1. **Reachability.** Every declaration named by the 228 formalized and definition rows exists on
   origin/main in a module the root reaches, and so does every declaration the row corrections
   add. The exception is `RingCompressionCellGeneral`, which is on the wire queue.
2. **Gate.** Each gate runs `#audit_closed_axioms` on every named-Prop endpoint and every closed
   theorem the census names in its range, and `#audit_axioms` on every other named declaration:
   - `Audit/Sec3.lean`: 130 `#audit_closed_axioms` and 177 `#audit_axioms`, covering 269
     distinct declarations. A declaration named by several rows is audited once per row.
   - `Audit/Sec4.lean`: 29 `#audit_closed_axioms` and 90 `#audit_axioms`, covering 102 distinct
     declarations.
   - Every import of `Audit/Sec3.lean` except the new carrier is in the root import closure at
     origin/main `07169dd31` (6217 modules, no dangling import). `Audit/Sec4.lean` is wired.

   The gates also cover the claim-making structural rows and the declarations the row corrections
   add.
3. **Reading against the print.** The carriers checked in detail:
   - `lem:ring-compression-cell` (tex 855–912): defect 1.
   - The concrete instance after `prop:clifford-locally-rf` (tex 1589–1610): defect 2.
   - Proof of `thm:full-defect-ring` (tex 936–943):
     - `EJZCitationSentences.PrintedUniversalRingBothGroupsPropertyT` states property (T) at the
       printed `G = EL₄(𝒞)` (`UniversalGroupB.B`) and at the printed `L`, the core on coordinates
       1,2,3.
     - It also states the surjection onto `L_{𝔽₂}(1,2)`, nontriviality, finite generation of `𝒞`
       and finite generation of `G`.
     - The theorem is closed, so neither `[EJZ, Theorem 1.1]` nor `[BHV, Theorem 1.3.1]` enters as
       a binder.
   - The Jacobson paragraph (tex 1122–1145, jacobson lane):
     - `PrintedJacobsonRadical` states `Rad_MF(EL_n(J)) = EL_n(J,JeJ) ≅ ⋃_N SL_N(𝔽₂)`, infinite,
       simple and locally finite, for `n ≥ 4`, as printed.
     - `PrintedJacobsonKernelFinitary` binds `2 ≤ n`, the range in which the paragraph uses
       `EL_n`. Its third clause ("acting on `V^n` as all of `GL_fs(V^n)`") needs a second
       coordinate.
     - `manuscriptSentence_jacobsonShiftAction` and `manuscriptSentence_jacobsonQuotientLaurent`
       state every clause of their sentences.
     - `blockAct_elGen_matUnit` gives the relative roots.
     - `blockAct_commutator_matUnit` gives the commutator
       `[e_ik(f_uw), e_ki(f_wv)]` at `w = v`, one witness for the printed "the commutator … of
       two".
   - Proof of `cor:leavitt-mf-quotient` (tex 1307, leavitt-units lane):
     - `PrintedKhanhThanhSentence` is stated for every field, which covers the printed countable
       field. It states all five clauses, and `[KhanhThanh, proof of Theorem 7.2]` is proved, not
       assumed.
     - `PrintedLeavittBothInclusions` states both inclusions and the triviality of every
       homomorphism from `EL_d(R)` to an MF group, for every countable field and every `d ≥ 2`.

## Defects

1. **Fixed: rows `718cc7b04afd` (L872), `c0383f82a141` (L888), `d1142160bf17` (L899) and
   `83ed5eb3b38c` (L904).**
   - `lem:ring-compression-cell` is printed for every unital ring `R` and every `s, t ∈ R` with
     `ts = 1`. The census carriers `FullDefectRingSentences.manuscriptSentence_compressorPieceDef`,
     `…_compressorInvertible`, `…_centralMark` and `…_centralMarkCentral` are stated only at
     `UniversalPair.pairInverse`.
   - `RingCompressionCellGeneral` states and proves each sentence for every ring and every
     `P : OneSidedInverse R`:
     - `printedCompressorPieces`: `u_i = e_{4i}(t-1)e_{i4}(1)e_{4i}(s-1)e_{i4}(-t)`.
     - `printedCompressorInvertible`: `u = u₃u₂u₁` is the displayed matrix, and that matrix is
       invertible.
     - `printedCentralMark`: `c = [e₄₁(e), e₁₄(t)] = diag(1,1,1,1+et)`.
     - `printedCentralMarkCentral`: `c ∈ C_G(L)`, along the printed route. Every element of `L` has
       the shape `diag(A,1)` (`core_isBlockDiagOne`), and `diag(1,1,1,1+et)` commutes with every
       such matrix (`centralMarkMatrix_commute_blockDiagOne`).
   - The row corrections name the new carriers first and keep the universal-pair instances.
2. **Fixed (`b9772f360`): rows `3229365c29c6` (L1589), `e947a3d4f4a1` (L1598), `80c65e0771e4`
   (L1608) and `c48c7da870a2` (L1608).**
   - The carriers of "`α(v,A) = (2v,A)`" and of "its image consists of the affine matrices whose
     translation coordinates are all even, so `[Γ̄ : α(Γ̄)] = 8`" were proved on
     `Monsters/AffineSL3Doubling.lean`. That is a separate semidirect product whose `alpha` is
     defined by doubling, so they say nothing about `ExplicitLinearModel.gammaBar` and `conjD`.
   - The display of `Γ̄` and the definition of `D` and `α` named no declaration.
   - `AffineDoublingLiteralModel` states and proves all four on `gammaBar ≤ GL₄(ℚ)` and conjugation
     by `dU`.
3. **Fixed by row correction: definition rows that named no declaration.** They are
   `5870021d2e03` (L806), `18fd64bafd97` (L1039), `60898a519f4f` (L1435), `c180c0186454` (L1435),
   `bc2d73bb124a` (L1539) and `e4ebdec3bbab` (L1548). The corrections name the declarations that
   carry the printed setup. The leavitt-units lane filled `dcf6fa4be4de` (L1298).
4. **Fixed by row correction: `77028123cdd6` (L1598).** The row named only
   `gammaBar_residuallyFinite`. The clause "it has property (T) [BHV, Example 1.7.4(i)]" is the
   closed `CommutingLampCollapse.gammaBar_hasKazhdanPropertyT`.
5. **Fixed by row correction: claim-making structural rows that named no declaration.** They are
   `19abb698ab4a` and `3a929e3e1455` (L788), `ded89cfcd0e4` (L1239), `d47b613bb096` (L1384) and
   `8e53d32e3fb8` (L1435).
6. **Fixed by row correction: rows naming only a `def … : Prop`, never the theorem that proves it.**
   They are `2ff745dd7064` (L1060), `eefa8a852d05` (L1239), `7ce8c636a470` (L924) and
   `18fd64bafd97` (L1039). Each correction adds the `…AllCharacteristics` theorem of
   `FullDefectRingEJZUnconditional` whose type is that Prop.

## W1 model tests (lead item, 2026-09-13 after the 08:30 restart)

The item: model-test and truth-audit the piece Props of W1 `hgreendlinger`, meaning the h94
pieces and the Euler-count chain. dgo-geometric covers the pocket Props and C3–C5.

1. **Landed `594d1e97a`: `GGT/VanKampen/Estimating/OsinCConditionLineModel.lean`.** Probe GREEN
   `0913-093823-13550` (BUILT); it is on the wire queue.
   - `D` is `ℤ` with alphabet `{±1}` and no subgroups, and it is 0-hyperbolic (`hyperbolic`).
   - `condition`: `{a^m, a^-m}` satisfies `OsinCCondition` whenever `λ ≤ 1`, `0 ≤ c`, `ρ ≤ m`
     and `2ε < μ m`. Since `ℤ` is abelian, the exclusion clause forces two different connectors,
     so every piece is shorter than `2ε`.
   - The closed endpoint `osinCConditionLineModel : OsinCConditionLineModelStatement` holds for
     every `0 < λ ≤ 1`, `0 ≤ c`, `0 < μ`, `ε` and `ρ`. So the C-condition layer of every piece
     assumption can hold at every threshold.
   - The earlier models on main, `UnboundSmallMuCounterexample.condition` and
     `UnboundConjugateCounterexample.condition`, fix `ε = 0` and one `ρ`.
2. **Case 1 (theoremc-retire): closes; the composition is not landed.**
   - `OsinLemma94CaseOneWalkStatement` is true as landed at `fd6ce3c09`.
     - `a < a'` is `source_forward`; `b' < b` is a hypothesis.
     - `walk` and `closed` give the two value equations.
     - `boundary_arc` puts the target inside one section.
     - Allowing any connector alphabet is harmless, because the conclusion names no connector
       word.
   - ko-closed proved it: `osinLemma94CaseOneWalk`, GREEN `0913-095509-55850`, bytes = main
     `8f0f73966`.
   - `osinLemma94CaseOneInput_of_walk` is GREEN `0913-093623-11190` at the bytes of `3292f7a20`.
     Composing the two proves `OsinLemma94CaseOneInput`, but no landed declaration composes them.
   - `OsinLemma94CaseOneSameCellStatement` is redundant.
     `RealizedSectionFamily.false_of_quadrilateral_face` has no hypothesis that the source and
     target cells differ, so `osinLemma94CaseOne_false_of_walk` already covers pairs whose sides
     have the same kind.
3. **Case 2 surgery (hull-unbound, sec5-sentences): no counterexample.**
   - `PendantPathRemovalInput`: `DegreeTwoJoints` makes the path a spur from a leaf. A spur that
     was a whole component would make the face the exterior.
   - `CornerInsertionInput`: a chain with the face on both sides cannot close up, so the inserted
     word splits the face into two unselected `G`-faces.
   - `SeparatingPathRemovalInput` is proved from the pendant form (`7d4a2515f`).
4. **Count piece (hull-count94).**
   - `OsinLemma94PolygonCoversInput` is closed, with `L = 24ε` (GREEN `0913-093648-12289`).
   - `OsinLemma94PolygonSideBudgetInput` is plausibly false, through the outward-spur mechanism
     hull-count94 reported. The candidate instance is below. It was sent to main, which holds
     the ruling.
5. **The Euler-count chain.** C1 `phiSubdividedMultigraphO` (`4e27d4965`), C2
   `card_add_six_le_of_linkedO` (`050822843`) and ghw-charp2's `hlinked` and `hV` producers are
   unconditional, and `DartMinimal` is sound.
6. **Not audited.** `TwoGonHoldsInput` (C6′, `4beca2743`): its route goes through the pocket Prop
   `EmptyTwoGonInput`, which is dgo-geometric's.

### Candidate counterexample to `OsinLemma94PolygonSideBudgetInput`

- **Setup.** `G = ℤ` with base alphabet `{±1, ±2}` and no subgroups; `λ = 1/2`, `c = 3`;
  `W = {1^m, (−1)^m}`.
- **Boundary word.** `u · (−1)^m · (−1)^{6t}` with `u = (2 2 2 1 −1)^t`. Its three sections are
  `(1/2, 3)`-quasi-geodesic.
- **Diagram.**
  - a `G`-face `f` with walk `2^{3t} (−1)^{6t}`, of value 0;
  - `t` outward spurs `1 −1`, rooted on the `2`-side of `f`;
  - one relator cell `(−1)^m`, at the far corner.
- **Why the hypotheses hold.**
  - With one cell, `Reduced` holds vacuously.
  - The boundary value is `−m ≠ 0`, so `LeastArea` holds.
  - No cell dart is on the walk of `f`, so `f` lies in no region. `f` cannot fold, since its
    labels are `2` against `−1`.
- **The polygons.** One polygon, and every side is an arc of `outerDarts`. Each spur root is a
  vertex of degree 3, where `facePerm (alpha e') ≠ alpha e`, so `Maximal` allows a split there.
  `short_region` cannot absorb these sides. So `∑ sideCount ≥ t + 1`, against `K n = K`.
- **Unverified.**
  1. Some optimal family on this diagram has card at most 9.
  2. The dart-minimal optimum keeps the spur roots on polygon walks. Every O-equivalent diagram
     reads the same word, and its `t` letters `1` allow at most `t` bridges.
- **Consequence.** The count grows with the section length `t` at every `ε`, `ρ` and `n`, so
  moving `∃ K` after `∀ ε` does not repair the Prop. Letting (A2) sides skip value-one excursions
  does.
- **Offered, not started.** A formal fixture for this instance. A one-cell `LeastArea` diagram
  over the line model, which would show that the hypotheses of `OsinLemma94SectionStatement`
  hold together.

## Open (owned by other lanes)

- `b6d1590be7ab` (L1145, partial, ghw-charp2): the GHW wall, reported to the lead.
  `GHW.ghwFinitelyGeneratedCharP` (`Kazhdan/GHWCharPClosed`) is now on main and root-reachable, but
  the row is still partial in `metadata/nm-census-rows/ghw-charp2.tsv`.
- `c149d33e8f7e` (L1145, partial, jacobson): `manuscriptSentence_twoResultsComplementary` is in
  `JacobsonComplementarySentence.lean`, which the root does not reach. ghw-charp2 queued it for
  wiring at `42d443298`.
- `dcf6fa4be4de` (L1298) and `7916c8696def` (L1307), partial, leavitt-units: they name
  `LeavittMFQuotientUnitsGL`, which the root does not reach. leavitt-units queued it for wiring at
  `4f629158e`.
- `3009704fef89` (L1145) and `a4b5b1a0504a` (L1008) moved from formalized to partial at the census
  merge, so the regenerated gate no longer audits them.
- Wiring: `RingCompressionCellGeneral`, then `Audit.Sec3`. Until the carrier is wired, the census
  merge grades rows `718cc7b04afd`, `c0383f82a141`, `d1142160bf17` and `83ed5eb3b38c` partial.
  - Probe `0913-040726-62527` ran at base `840e6a1d8`. Up to origin/main `39dd43b39`, the gate's
    import closure has 1033 modules, and only the two probed files changed, at the probed bytes.
    So that probe stands for one at the current base.
  - The root already imports `Algebra.PreusserSandwichExchange` and
    `NonMFSentences.AmenableTraceSentencesB`, so neither becomes root-reachable only through a
    gate. The only module the gates newly make reachable is `RingCompressionCellGeneral`.
