# go-lemma42 (lane report, 2026-09-11)

Scope (lead correction ~21:15): take over `Manuscript/NonMF/GerasimovaOsinLemma42Proof.lean` from
dgo-geometric, make it compile, land it; no second Lemma 4.2 proof.

## State of the files
- `GerasimovaOsinLemma42Proof.lean`: origin 110ba458c (md5 80b0c6fd…); latest = attic 2b7e8298d = shared tree
  (md5 b53ff9d9…). Docstring-only change: route note, and "no census row of its own" in place of `partial`.
- `GGT/GerasimovaOsinCyclicTwoSided.lean` (dgo-geometric's, READ-ONLY here): origin 7561321b…; latest = attic
  4ac077236 = shared tree (md5 350bd666…). Repair: `Elementary.base_subset_alphabet_carrier` (outside the import
  closure) replaced by `Set.mem_union_left _` at lines 237 and 318.
- Both latest bytes are in dgo-geometric's probe 0911-210846-20111 (SLURM 435379, acn141, base 4ac077236).

## Probe results
- 0911-210846-20111 (dgo-geometric's, base 4ac077236): `GerasimovaOsinCyclicTwoSided` BUILT [9879/9879] (558s), in
  COMPILED evidence with md5 350bd666. The probe FAILED only on PNaivePingPong (outside this closure).
  `GerasimovaOsinLemma42Proof` was not in its module list: NOT built yet.
- go-lemma42 wrapper probe: queued behind nm-b preparation (background waiter, re-reads the clone assignment).

## Checked by reading
- The theorem is closed: no hypothesis left open. `HasTrivialFiniteRadical G` unfolds to exactly the `hrad`
  binder of `exists_cyclic_hypEmbedded_twoSided`. `coneOffFamily A K` has `base := A.carrier` and
  `RelGenSet.alphabet D = ⟨D.base ∪ ⋃ fam, _⟩`, so the `Set.mem_union_left` repair and `D'.base` uses are definitional.
- Imports: CyclicWord and LoxodromicCyclicEmbeddedAvoiding compiled (replayed in the probe);
  GerasimovaOsinGeometricInputs compiled (go-sr1).
- The probe's red module PNaivePingPong (sorryAx at 164) is outside this closure.

## Census
No row: Lemma 4.2 is internal to the cited proof of GO Theorem 1.1. The printed sentence (tex 1729–1731,
cor:regular-nonmf-algebra) is graded through `GerasimovaOsinTheorem11Printed`.

## LANDED
- 5558478e0 `Manuscript/NonMF/GerasimovaOsinLemma42Proof` (probe 0911-213026-69780, cs-simplicity, BUILT 43s). CyclicTwoSided
  landed by dgo-geometric at 2ec9cfdba. Lemma 4.2 is closed; nothing is left as a hypothesis.
- b8af8cb13 census merge (map, register, census tsv/md) at origin 434d65bfb: 323 formalized / 51 definition / 46 structural /
  19 provenance / 18 attribution / 36 partial / 5 unassigned. verify-decls 0 missing of 811; verify-unconditional
  189 accepted, 0 new.

## Census tooling (census/)
census_merge.sh (acn112 via msi; live work dir merge-live, delta sync), merge_rows.py (sentence start-line location,
statement-env rows, unions, compiled-evidence downgrade incl. clone oleans), overrides.tsv, baseline-merge.txt.

## TRAPS
- nmland.sh rewritten mid-run: bash reads scripts lazily, so a run printed LANDED-like output and a landed.log line
  for a commit that never reached origin. Always check `git merge-base --is-ancestor <sha> origin/main`.
- sentence_census.py records PARAGRAPH start lines; lanes' LINE:<n> keys need the sentence's own start line.
- f57b559f7 census merge step (rows from metadata/nm-census-rows, 13 lanes): unions per sentence, register.py (10 lines),
  verify-unconditional 236 accepted / 0 new. census_merge.sh lands every step (rule 21) and verifies the sha on origin.
- 0911-231324-58545 PROBE GREEN: BinaryExampleSentences, IntroSentences, KorchaginFullSequenceSentence compiled unchanged
  (bytes = origin; nothing to land). Wire candidates (0 importers).
- 91fbada58 GroupTheory/HydeLodha/QTwoBrownTriangle (probe 0912-003620-69441 GREEN): vertexH_triangle (htri for simple-group),
  exists_commutator_compactCore_move, exists_edgeStab_left, resLabel, triKey, triKey_eq.
- TRAP: `open Classical in` must precede the docstring (a docstring followed by `open ... in` is a parse error).
