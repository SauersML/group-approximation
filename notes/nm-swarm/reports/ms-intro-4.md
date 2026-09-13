# Lane ms-intro-4: tex 295–357 (thm:torsion-free, Related work)

Lead: session nonsofic-existence-49 (wave 2). Range at origin/main 68481e4d7. Census rows are matched by text; the
generated census still carries the pre-chain-core line numbers (285, 291, 298, 324).

## Sentence ledger

| key | tex | status | verdict |
|---|---|---|---|
| `0f22bdbc4184` | 297–300 thm:torsion-free statement (incl. "In particular, no nontrivial quotient of Q is MF") | partial | W1 wall. `_of_greendlinger` forms (TorsionFreeGreendlingerLeaf, TorsionFreeGreendlingerForms) over hgreendlinger alone; hbridge, hKO, hW closed. Owners: the W1 waist lanes of the other swarm (8 residual binders, roster 14:50–16:17). Not rebuilt here. |
| `27e0c2f96db3` | 303–305 "Section builds Q from FFF §2 and Hull" | attribution | Honest: construction summary; the mathematics is carried by the thm:torsion-free rows. |
| `dce7a9ff4e83` | 305–306 "Its reduced C*-algebra is simple, unique trace, stable rank one, not MF" | partial | W1 wall, same binder and owners as `0f22bdbc4184`. Not rebuilt here. |
| `27d456b915c0` | 310–311 BK94 abstract | attribution | Honest (history). |
| `5d8b94bc850e` | 311–313 NF / strong NF / nuclear stably finite might coincide | attribution | Honest (history). |
| `14ee41b7f3cc` | 313–315 BK97: NF iff nuclear and MF | attribution | Honest: a cited theorem, not used by any proof in the paper. |
| `82cac0c03a39` | 315–318 quasidiagonality question; TWW answers it under UCT + faithful trace | attribution | Honest: not used as a proof step. |
| `ba77c51e9726` | 319–321 the MF problem | attribution | Honest (history). |
| `6edef6dc2d68` | 321–325 positive answer ⇒ every countable group MF | formalized | PASS. `manuscriptSentence_positiveMFProblemAnswerMakesEveryCountableGroupMF` (IntroSentences, root-imported, `#audit_closed_axioms`); faithful conditional form, proof via `reducedGroupCStar_separable_stablyFinite`. |
| `c8241b12c037` | 325–327 CDE introduced MF groups; question open | attribution | Honest (history). |
| `abfcbcb3af2b` | 327–332 MIP*=RE ⇒ separable stably finite non-MF algebra (GH Prop 6.1, Rem 6.2) | formalized | PASS for the mathematical conclusion: `printedNegativeConnesEmbeddingSentence` (PriorWorkConnesEmbedding, root-imported, audited) proves existence through the paper's own reduced group algebra. The printed route (MIP*=RE, GH 6.1) is credit by lead ruling 09-12 and is consumed nowhere. |
| `4c82f6049796` | 332–334 thm:headline gives a counterexample among reduced group C*-algebras and answers the group question | formalized | PASS. `manuscriptUnitGroupHeadline : PrintedUnitGroupHeadline` (root-imported, audited) contains ¬IsCDEOperatorMF and separable ∧ stably finite ∧ ¬IsMFAlgebra for C*_r. |
| `213a6657c8ff` | 336–339 configuration of OAI Prop 2.3 | attribution | Honest. |
| `de554b7cd342` | 339–342 soficity, Kun, Kun–Thom, V | attribution | Honest: describes OAI's proof, not used here. |
| `523f02126056` | 343–349 rigidity from the Kazhdan projection in a stably finite corona; commutator killed in HS norm; thm:normal-kazhdan | formalized | PASS after re-grade. New closed carrier `RelatedWork.manuscriptSentence_relatedWorkKazhdanRigidity` LANDED 4dd8eb24d (probe 0913-165558-33390 GREEN, `#audit_closed_axioms`); queued for wiring. See below. |
| `b89e90ea6607` | 349–351 H is OAI's group; FFF configuration | attribution | Honest. |
| `9e2046c330c8` | 351–353 BDL Prop 1.5 | attribution | Honest: not used. |
| `ea89f566cf20` | 353–354 compression relation replaces stability | structural | Honest. |
| `a494a9e94d28` | 354–356 Eckhardt's note | attribution | Honest. |

## Finding on `523f02126056`

The row names five carriers. Two of them prove adjacent sentences, not this sentence's clauses:
- `manuscriptSentence_coronaKazhdanComplementIsInvariantCorner` is the NORMAL-K corner statement from the paragraph after
  thm:compression-criterion. The printed clause here is about the Kazhdan projection of L commuting with the compressor
  because the corona is stably finite.
- `manuscriptSentence_kazhdanInequalityKillsCornerOnDefect` is sentence `0418dd5f3a67` (the corner vanishes). The printed
  clause here is that every operator norm asymptotic representation sends the defect commutator to 1 in HS norm.
- The faithful carriers already exist on main: `TransportProjectionCommutation.commute_sigmaB_projection`,
  `manuscriptSentence_stableFinitenessGivesProjectionEquality`, `manuscriptSentence_defectAsymptoticallyTrivialInHS` and
  `manuscriptSentence_commutatorHilbertSchmidtVanishing`.
- `KazhdanTransportSentences.lean` and `RankTwelveConfiguration.lean` carry no `#audit_axioms` lines.

CLAIM `523f02126056` closed carrier: GroupApproximation/Manuscript/NonMFSentences/RelatedWorkKazhdanRigidity.lean

## Landed

- 4dd8eb24d `GroupApproximation.Manuscript.NonMFSentences.RelatedWorkKazhdanRigidity` (probe 0913-165558-33390 GREEN).
  - `def PrintedRelatedWorkKazhdanRigidity : Prop` has four conjuncts in printed order: `commute_sigmaB_projection`;
    `manuscriptSentence_commutatorHilbertSchmidtVanishing`; `RankTwelveEndpoint.PropositionDefect`; clause one of
    `manuscriptOneSidedCompressionCriterion`.
  - `theorem manuscriptSentence_relatedWorkKazhdanRigidity` carries `#audit_closed_axioms`. The module also audits the
    consumed `commute_sigmaB_projection` and `manuscriptSentence_commutatorHilbertSchmidtVanishing` (`#audit_axioms`) and
    `manuscriptOneSidedCompressionCriterion` (`#audit_closed_axioms`).
  - Wire queue line appended. Census row `523f02126056` is in `metadata/nm-census-rows/ms-intro-4.tsv`.

## Range status

Every sentence of tex 295–357 is carried by a closed root-reachable declaration or honestly classified, except the two
W1-wall rows (`0f22bdbc4184`, `dce7a9ff4e83`). Those wait on hgreendlinger, which the other swarm owns. The new module
becomes root-reachable when root-wire wires it.

## Item 2: help W1 binder 7 (agreed with w1-binder-7, 17:3x)

CLAIM first-turn order across the edge doublings: GroupApproximation/GGT/VanKampen/Estimating/OsinPocketEdgeDoublingFirstTurns.lean (new module).
- `EdgeInsertion` rotation on embedded darts, and first turns transport along `embed` for distinct corners;
- the first-turn chain of a pocket survives `faceEdgeDoubling` (hull-respell) and `faceEdgeDoublingInside` (ghw-assembly).
  The chain condition is stated inline; the unregistered draft `OsinPocketPinchFirstTurn` defines `PocketFaceSet.FirstTurns`, which this module does not redeclare.

### LANDED c2927f84f (probe 0913-175826-70210 GREEN, BUILT and COMPILED)

`Estimating/OsinPocketEdgeDoublingFirstTurns` is new and unwired, and is queued for wiring. It certifies no printed sentence,
so it adds no census row.
- `EdgeInsertion.sigma_embed_apply`, `sigma_none_apply`: the rotation after an edge insertion at distinct corners `a`, `b`.
  The new dart `some none` sits just before `a`, and `none` just before `b`.
- `EdgeInsertion.exists_sigma_step_lift`, `exists_sigma_pow_lift`: `k` old rotation steps become `k2 >= k` new steps. Every
  dart passed strictly inside the new run is new, or the image of a dart passed strictly inside the old run.
- `EdgeInsertion.walkKeep_map_embed_iff`, `not_walkKeep_map_embed_none`, `not_walkKeep_map_embed_some_none`.
- `EdgeInsertion.firstTurn_embed`, `firstTurn_reverse_embed`, `firstTurnChain_map_embed`: first turns, and the first-turn
  chain of a boundary cycle, lift across the insertion for `a != b`.
- `PocketFaceSet.faceEdgeDoubling_firstTurnChain` (the doubling outside `K`, hull-respell) and
  `PocketFaceSet.faceEdgeDoublingInside_firstTurnChain` (the doubling inside `K`, ghw-assembly). Neither takes hypotheses
  beyond those of the construction. The chain condition is stated inline, in the spelling of `firstTurnWalkPocketInputs`
  on `cycle.reverse.map alpha`; it is exactly the body of `PocketFaceSet.FirstTurns` in the unregistered draft
  `OsinPocketPinchFirstTurn`.
- Model check, on paper: a lifted turn changes only at a rotation step into a corner, where it gains one step past a new
  dart. Neither new dart lies on an image walk, so the turn is never cut short. `corners_ne` rules out equal corners,
  because the second corner has index 1.
- Arcs map through the dart embedding, so no arc length changes. Nothing to report to w1-binder-7's full-arc claim.

Next in this item: none. Ready for the next leaf.
