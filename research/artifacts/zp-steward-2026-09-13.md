# ZP steward log, 2026-09-13

Steward lane: z-steward. Every check runs `tools/cairn.py check` on MSI, in a `--shared` clone of the
live `origin/main` tip on scratch (`/scratch.global/sauer354/zp/steward/`). Root status comes from the
compiled `.cairn/cache/graph.json`. `cairn why` is recorded for every root that reads established.
Roots are the 62 numbered roots of RULES §1, plus 2.15b and the hub `zaremsky-open-problems-2026-07-12`.

## Check c1: tip c028e86895, started 15:27 CDT

| item | value |
|---|---|
| tip | `c028e86895121a57f834ea57a4f69ffd3ffe853c` |
| EXIT | 0 |
| ERRORs (whole graph) | 0 |
| ERRORs naming zaremsky-region files | 0 |
| WARNINGs (whole graph) | 28 |
| compiled | 10719 claims + 10928 routes |
| numbered roots present | 31 of 62 |
| hub `zaremsky-open-problems-2026-07-12` | OPEN, reachable |
| routes into roots with `requires: []` | none (local scan at 315b95e0c2 too) |

Established roots, each derivation read from `cairn why`:

| root | via | derivation | review |
|---|---|---|---|
| 1.02 | `zaremsky-1-02-by-no` | `some-type-f-group-has-unsolvable-word-problem` (citation) | list-answered import |
| 1.15 | `zaremsky-1-15-by-stallings-bieri` | `stallings-bieri-groups-have-quadratic-dehn-function` (citation) | PASS, zp-review-topology part 1 §2 |
| 1.23 | `zaremsky-1-23-by-no` | `raag-kernel-dehn-function-below-bestvina-brady` (proof) ← `bestvina-brady-dehn-function-classification` (citation); `zaremsky-1-23-by-yes` INVALIDATED | UNREVIEWED new answer (z1-23-bb-dehn, fbb779bc37) |
| 2.06 | `zaremsky-2-06-by-hyde-skipper-zaremsky` | `stein-group-f23-does-not-embed-in-thompson-v` (citation) | list-answered import |
| 2.15 | `zaremsky-2-15-by-klein-bottle-group` | `klein-bottle-group-embeds-in-v-but-not-in-f` (proof) | list-answered |
| 2.17 | `zaremsky-2-17-by-no` | `thompson-t-has-no-subgroup-isomorphic-to-t-times-t` (proof) ← `finite-subgroups-of-thompson-t-are-cyclic` (proof) | list-answered |
| 4.03 | `zaremsky-4-03-by-virk` | `rips-complexes-of-integer-lattices-are-contractible` (citation) | PASS, zp-review-topology part 1 §1 |

- Six established roots are the list's own answered problems. That is intended.
- 1.23 is the one establishment of an open problem. It goes through a real proof route: the suspension of
  the path C–D–E–F, character 0 on A, B and 1 on C, D, E, F, kernel `F_2 × BB_P` quadratic, `BB_Γ` cubic
  by Chang–García-Mejía–Migliorini (arXiv:2507.07566v2, Corollary 1, Figure 1 example Γ_1). It is not a
  placeholder establishment. It stays "unreviewed" until a verifier PASS lands.

WARNINGs naming zaremsky-region files. None of them gates the graph:
- restatement lint on single-prerequisite answer routes: `zaremsky-1-03-by-yes`, `zaremsky-1-19-by-yes`,
  `zaremsky-2-06-by-hyde-skipper-zaremsky`, `zaremsky-4-06-by-yes`. This is the shape the root template
  prescribes (question root ← answer claim), so it needs no action.
- possible duplicates among the 2.04 part claims `thompson-f-qi-to-f-times-f-resolved`,
  `thompson-f-qi-to-f-times-z-resolved`, `thompson-f-qi-to-thompson-t-resolved`,
  `thompson-f-quasi-retracts-onto-f-times-{f,z}-resolved`, `thompson-t-quasi-retracts-onto-f-resolved`
  (similarity 0.29–0.42). `check --changed` escalates these to policy errors for changed files; the
  owner answers them with `distinct_from`.

Roots missing at c028e86895: 1.01, 1.06, 1.07, 1.09, 1.17, 1.20, 1.21, 1.24, 2.07, 2.09, 2.10, 2.11,
2.12, 2.13, 2.16, 2.18, 2.19, 2.20, 3.01, 3.02, 3.03, 3.04, 3.06, 3.08, 3.09, 3.10, 4.01, 4.02, 4.04,
4.05, 4.07, and 2.15b. By the later tip 315b95e0c2 (local `ls-tree`), 1.01, 1.07, 1.21, 2.13, 2.16, 2.18,
2.19, 4.02, 4.04 and 4.07 had landed. The next check records the full list.
