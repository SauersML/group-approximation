# ms-sk-open
Direction: SK census rows that are not truly closed (open row, conditional or stub "formalized" rows, attribution rows that assert mathematics). Prefix: GroupApproximation/Manuscript/SimpleKazhdanSofic/SkOpen/ (LEAN-OWNERS).

## Audit (origin/main c7f12fba7..ddeea47ea, source read, not built)
- **166 formalized rows, 428 distinct decls.**
  - Every row cites at least one theorem.
  - No cited theorem binds a `…Statement`/`Owed`/`Gap` hypothesis. The only binders are printed mathematical hypotheses: `ozawa_not_hasLocalLiftingProperty` (hT, hH) and `not_hasLocalLiftingProperty_of_not_hasFactorizationProperty` (hH, hF). `printedSimpleKazhdanSoficMain_of_pieces` is cited alongside closed decls.
  - No cited Prop def is an implication out of another Statement.
  - No sorry, admit or axiom appears in the 139 cited files.
  - Build attestation is items 1–3 (ms-green-sk, ms-sk-uncond-a/b); I did not duplicate it.
- **Open row `768ac9454e9b`** (l.733–735): conditional on the stable K₂ chain (the LVCohn*/LVFreeAlg*/SKFix01 frontier and LVPolyK2). Zone B plus ms-sk-uncond-a. Not closable here without duplicating their work.
  - MS-WORKLIST item 4 (K₂ commutes with filtered colimits; K₂ of a product) ALREADY EXISTS in the needed form:
    - `LVCohnK2/DirectedUnion.stableK2Trivial_of_subrings` (directed unions of subrings);
    - `LVCohnK2/Products.lean` (finite products).
  - So item 4 is redundant.
- **Attribution rows whose mathematics is already closed** (candidates for regrading):
  - `503221e301f6` (Stepanov route): `Full.StepanovMatui.printedStepanovRouteSimplicity`, `printedSubshiftRingPairDependence`;
  - `8212b1470040` (Kionke–Schesler + Wilson): `SimpleKazhdanSofic.Audit2.manuscriptSentence_simpleLEFHostsWithoutT`;
  - `fc84c012b409`: clauses (a) and (c) are `SimpleHosts.Endpoints.manuscriptSentence_countableGroupEmbedsInFGSimpleGroup` and `manuscriptSentence_simpleKazhdanGroupContainsEveryFPGroup`. Clause (b) rides the GL waist (zone B).
- **Stale docstring:** `LEFCorollaries/WordProblemHosts.lean` "Remaining gap" (the lamplighter host WP upper bound). It is closed by `LamplighterWP.hostProof` and `Full.SK11.lamplighterHostSolvableWP`.

## Closing (this lane)
- `aaf5fe1a98c3` (Arzhantseva ARF): SkOpen/Arzhantseva.lean.
  - Definition 9 was read at the published source (Springer PDF via MSI).
  - `manuscriptSentence_arzhantsevaAsymptoticallyResiduallyFinite`: an infinite simple Kazhdan ARF group exists, and LEF ⇒ ARF and RF ⇒ ARF for fg groups.
  - Probe pending.
- `9fe4e2896405` (Boone–Higman in Thompson's form): SkOpen/BooneHigmanThompson.lean.
  - Plugs `LamplighterWP.hostProof` into `ThompsonConstruction.…_of_printedLamplighterHostSolvableWordProblem`.
  - Result: `manuscriptSentence_booneHigmanThompson`, the unconditional fg Boone–Higman–Thompson equivalence (uses the repo's Higman embedding theorem).
  - Probe after the first one.

## Not closable in scope (literature theorems about topological full groups)
- `e5932a45f053` (Grigorchuk–Medynets: WP([[T]]') solvable ⇔ L(X) recursive). The ⇒ direction needs effective generation of [[T]]' (Matui), which is multi-kLOC.
- `3eaee0a2dc7e` (Matui Lemma 3.4 / Theorem 4.9): the same infrastructure gap.

## Census row → decl mapping (for the census regrade; gqland refuses metadata/)
- aaf5fe1a98c3 → GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.manuscriptSentence_arzhantsevaAsymptoticallyResiduallyFinite (after green)
- 9fe4e2896405 → GroupApproximation.Manuscript.SimpleKazhdanSofic.SkOpen.manuscriptSentence_booneHigmanThompson (after green)
- 503221e301f6 → GroupApproximation.Full.StepanovMatui.printedStepanovRouteSimplicity
- 8212b1470040 → GroupApproximation.SimpleKazhdanSofic.Audit2.manuscriptSentence_simpleLEFHostsWithoutT

## 09-18 ~21:15 (after restart; SLURM-BLOCKED)
- Both modules are on main, byte-identical to the lane files: Arzhantseva in e7fff6d62e, BooneHigmanThompson in 8d6acdcd0c. Neither is root-wired (ms-map wires only after a green build).
- No probe has built them yet. The v3 and v4 waiters were cancelled by the coordinator. The empty-overlay request 1789778213.65131 is queued; batch 1338076, now running, does not include it.
- FIX-GRAPH lists both as UNPROBED.
- Re-probe once SLURM-BLOCKED is gone. If red, fix and land the fix via gqland-lean.sh.
- Remaining rows (no work in this lane):
  - 768ac9454e9b: K₂ chain; ms-sk-uncond-a with fix node research/fix-sk-cohn-stable-k2-degree-zero-surj.md.
  - e5932a45f053, 3eaee0a2dc7e: topological full group infrastructure (Matui generation).
  - fc84c012b409(b): GL waist.
  - 2745cd64eada: history sentence. Its content is the next two rows.
- ~21:25: probe of request 1789778213.65131 came back DEFERRED (sbatch rejected, AssocMaxSubmitJobLimit). No re-probe loop; re-probe both targets once SLURM-BLOCKED is gone.
