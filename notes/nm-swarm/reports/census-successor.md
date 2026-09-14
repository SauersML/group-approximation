# census-successor: census merge after the census lane stopped

Lane ms-cite-2 acts as census-merge successor (main's item, 2026-09-13 ~18:25 CDT).

- The census lane has been stopped since its coordinator went down at 17:56.
- The last census landing before this successor was 6457b79e5 (14:17, base 36ff632cd). It carried the manuscript hash
  from before 45483f699, with 498 sentences.
- Merge 0913-171131 (base 4af014f74) did not land: REGISTER exited 3 on two unclassified findings.

## Procedure (gates unchanged)

Every pass runs on MSI through the census tools, detached on the node and polled for `SENTINEL=done`:
1. `merge_rows.py` unions the row files per sentence, applies compiled-evidence and root-reachability downgrades and
   restorations, and applies `overrides.tsv`;
2. the census tsv and md are regenerated;
3. `register.py` keeps `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt` in step;
4. worklist, `--check`, `--verify-decls`, `--verify-unconditional`.

The script lands the map, the register, the census tsv and md and `notes/nm-swarm/WORKLIST.md` as lane `census`, with
`NM_BASE` set to the export sha. It lands only when MERGE, WRITE, REGISTER, WORKLIST, VERIFY_DECLS and VERIFY_UNCOND
are all 0, and only when the shared tree's copies equal origin at the export sha. `--check --require-complete` stays
red on partial and unassigned rows, which is the true state.

## Successor changes

The tools are copied, not edited in place, to this session's scratchpad `ct/census/`, with the originals kept as
`*.orig`. Rows, evidence records, `landed.log` and `nmland.sh` stay in the census lane's scratchpad.

- **LINE keys of the new lanes.** `census_linemap.py` carries `LINE:<n>` from the tex at a8cc132c8 (before
  45483f699). The lanes launched by session nonsofic-existence-49 (`ct-*`, `ms-*`, `w1-*`) number LINE keys at the
  current tex (68481e4d7 and later).
  - Merge 0913-171131 carried ct-rank-budget `LINE:1700` to 2185 and skipped nine ct rows as ambiguous.
  - `merge_rows.py` now reads LINE keys of lanes matching `CURRENT_TEX_LANES` (default `^(ct|ms|w1)-`) without the
    line map. Other lanes keep the a8cc132c8 map.
  - The trial after the fix resolved every ct row.
- **Register rules.**
  - Two specific rules for the open assembly of `cor:dynamic-rank-budget`: `PrintedDynamicRankBudget` and
    `printedDynamicRankBudget_of_pieces`, which name the eight residual piece Props and their owners.
  - A guarded rule for the open named residuals of the chain-core tail (`ChainCore.*`, `ClopenCrossedProduct.*`). It
    registers a carrier-data, open-predicate or buried-conditional finding only when every row citing it is graded
    partial or open in the census the merge just wrote. The line names the premises and owners. A finding cited by a
    formalized or definition row stays UNCLASSIFIED, so the gate stays red.
- **Overrides**, effective at the next merge.
  - chain-itinerary is down, and ms-compress-1 re-graded three of its rows at bd7b20b28, carrying each old residual.
  - DROP overrides remove chain-itinerary's rows on `fe2bd83087c0`, `ed348643e2ad` and `807793f12a5e`, so
    ms-compress-1's rows grade those sentences instead of a union with the stale partial rows.

## Merges

| merge | base | result | formalized | definition | structural | partial | unassigned | total |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0913-183126 (trial) | e336f6734 | no land: REGISTER=3, 17 unclassified (chain-core tail residuals) | 299 | 51 | 51 | 193 | 86 | 717 |
| 0913-185744 | da89370bf | **LANDED b75e5bbcd**, verified on origin | 299 | 53 | 51 | 197 | 80 | 717 |

Merge 0913-185744:
- **Register:** 3 stale lines removed, 201 revised, 30 new registered, 0 unclassified.
- **Verifiers:** `--verify-decls` 0 missing; `--verify-unconditional` 468 accepted, 0 new.
- **Downgrades from origin's map:** 49 formalized, 5 definition and 4 structural rows went to partial. Every one
  carries a merge note.
  - Of the 197 partial rows, 169 are partial only because a carrier module is compiled outside the
    `GroupApproximation` import closure.
  - Most of those come from ms-* re-grades that name new, not-yet-wired carriers. The next merge after wiring restores
    them.
- **Unassigned (80):** 77 in sec:chain-core, 3 in the Introduction.

## Re-merge triggers

- After each ROOT GREEN wiring wave by ms-core-5, the root-wire successor (`notes/nm-swarm/reports/root-wire-successor.md`).
  - A wave lands as a "Wire N landed non-MF campaign module(s) into the root" commit on `GroupApproximation.lean`.
  - The last one was c0c1a8e3d (wave 16, 16:32). Wave 17 (15 ct/ms modules) was launched ~18:27 and is not on main at
    19:10.
- Whenever lanes land rows, and at least every ~2 h.
