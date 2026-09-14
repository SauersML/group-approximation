# Cairn steward orphan sweep, 2026-09-14

User order: "make sure everyhting is in Cairn". This sweep checked every `research/*.md` file that a lane of
coordinator session 829306b2 wrote with Write or Edit since 2026-09-12, against origin/main.

## 1. Sweep and triage

- **Swept:** 747 lane transcripts. 156 research paths were written but absent from main.
- **Excluded:** 22 of them belonged only to lanes still running at sweep time, and were left for those lanes.
- **Triaged:** the remaining 134 rows fall into four buckets.

| bucket | rows | meaning |
|---|---|---|
| ON-DISK-LAND | 71 | Finished (or dead) lane's file in the shared checkout, identical to the transcript's final version. Landed. |
| RECOVER | 9 | No copy on disk. Rebuilt verbatim from the transcript (last Write plus later Edits, following scratchpad copies after `mv`). Landed. |
| SUPERSEDED | 37 | The lane renamed or rewrote it, and the successor is on main. Examples: `three-positive-relations-allow-positive-scl` (58467f62d), `short-balanced-trivial-presentations-are-trivial-or-ak3`, `nonpositively-curved-simple-complexes-are-developable`. Also 12 `nh-unit-type-valuations` drafts whose results sibling lanes landed first. |
| DROP-DRAFT | 17 | Explicitly abandoned, with transcript evidence (see below). Not landed. |

The DROP-DRAFT evidence, by lane:
- **leavitt-tensor-coherence (9 files):** "Withdrawn proof. My local induction was wrong, so I deleted its 9 files without landing any of them."
- **bh-forces-unbounded-fp-simple-wp-complexity and its route:** removed with "Retire my duplicate Boone-Higman complexity root in favour of the peer's".
- **bkm-noise-test pair:** removed, replaced by `bkm-test-transparent-on-learnable-games`.
- **cantor-homeomorphisms-solve-unimodular-equations-internally:** "removed-unlanded-draft".
- **Three fpbs far-halfspace / half-graph drafts:** "removed (superseded) unlanded".

## 2. Landed commits (all blobs verified against origin/main)

| commit | lane | files |
|---|---|---|
| 3f7fb3c61 | kl-schur-universal | 8 |
| 3c2b6de5a | hl-whitehead-relative | 16 |
| 6491ebaab | hl-kl-certificate-search | 1 |
| 33b01f49e | kl-nonamenable-shapes | 8 |
| ff757f44a | solve-fp-intermediate-growth | 8 |
| 27b4b6318 | type-a-invariants | 7 |
| 13b630679 | kl-nonce-factors | 8 |
| 9266d93f2 | solve-covered-cantor-module | 2 |
| 9e85b42ab | bh-solvable-general | 5 |
| 2a433b12e | idempotent-charp | 6 |
| 345733f30 | solve-magnus-graph-builder | 17 (incl. 13 script and output files) |
| af95f4d16 | s9-bh-q59-a2 (`a2-kernel-removal-iff-image-satisfies-pbh`) | 1 |
| c96a3d131 | bs-f2xz-all-generating-sets | 2 |
| 389cd6d87 | zero-divisor-nup-hosts | 6 |
| 0f91f563e | steward fix (restored `artifacts:` key in four Linton nodes) | 4 |

Most of these lanes died on `model_not_found` or before their MSI Cairn check returned. None had landed.

**Special case.** `a2-kernel-removal-iff-image-satisfies-pbh` was the missing claim behind three errors that every
lane's full `cairn check` hit. Its proof route and two dependants were already on main (53113495c). Recovering it
removed those three errors.

## 3. Mechanical edits made during landing (no status label changed)

- **Renamed ids over 64 characters,** with references in the batch updated:
  - `adian-lot-presentations-with-acyclic-initial-or-terminal-graph-are-dr` → `adian-lots-with-acyclic-initial-or-terminal-graph-are-dr`
  - `lot-disjoint-maximal-sub-lots-relatively-injective-transfer-asphericity` → `lot-disjoint-sub-lots-relatively-injective-transfer-asphericity`
  - `nonsingular-coefficient-kernel-lies-in-locally-indicable-residual` → `nonsingular-coefficient-kernel-in-locally-indicable-residual`

  The old long-id files were moved out of the shared checkout into the steward scratchpad backup.
- **Artifact references that were never written** were removed, and a one-line note was added to each affected
  body (26 nodes). No transcript ever wrote these three files:
  - `research/artifacts/hl-whitehead-relative-pins-2026-09-13.md`
  - `research/artifacts/bh-solvable-general-2026-09-13.md`
  - `research/artifacts/one-relator-linton-graph-certificates-2026-09-13.md`

  The citation routes of hl-whitehead-relative therefore carry their quoted statements but not the pin file.
- **One `distinct_from` entry** of `a2-kernel-removal-iff-image-satisfies-pbh` named a route
  (`pbh-via-bh-and-a2-kernel-removal`), and was removed.
- **zero-divisor-nup-hosts' merged additions** to two existing nodes were replayed onto main (untouched since
  7e4ff5d66, 09-12 16:45) and landed in 389cd6d87:
  - `kaplansky-zero-divisor-conjecture` gains the sorted list of known groups without unique products;
  - `zero-divisor-host-is-not-virtually-compact-special` gains the pinned Martin–Steenbock status.
- **Not replayed:** its note on `e33-no-unique-product-pairs-of-small-radius` about a `(2,5)` job "pending" since
  2026-09-12, which is stale.

## 4. Cairn check

- **Baseline** (main 511f56c31, before the sweep): 8 ERROR lines, `compile failed`, exit 4. They comprised:
  - 3 lines on the missing `a2-kernel-removal-iff-image-satisfies-pbh` (fixed by af95f4d16);
  - 4 lines on Bowen–Chapman `.lean` artifact paths;
  - 1 line on `lot-at-most-six-vertices-census-proof` (`requires` mandatory), fixed by its lane at e9bd5559c.
- **After the sweep** (73a457ec7): 9 ERROR lines.
  - 4 were caused by the sweep itself: the frontmatter of the Linton nodes, fixed in 0f91f563e.
  - 4 are FOREIGN: `bowen-chapman-ambient-rank-models-do-not-round-peripheral` (94eaa7bea) and
    `bowen-chapman-witness-is-kt-double-at-q2-r3-d3` with its proof (91acaa96f), both from session
    01UM7nByUPBRzW6q2CVrVhTz. They cite `GroupApproximation/BowenChapman/{ResiduallyFiniteSubstitution,LaurentPair,Endpoint}.lean`,
    which are absent from main.
  - 1 is from this session but belongs to a lane that is still running: `leavitt-rooted-defect-window-carries-no-strict-design`
    (e39a422ba, lane gk3-leavitt-nonlinear) has `requires` on a claim. It was left to that lane.
- **Warning introduced by the kl-schur-universal batch** (a warning, not an error): a dependency cycle
  `kervaire-laudenbach-nonsingular-conjecture -> universal-schur-injectivity-for-nonsingular-adjunctions -> kervaire-laudenbach-nonsingular-conjecture`,
  from the equivalence routes of `kl-iff-acyclic-torus-amalgam-schur-injectivity`.

## 5. Final compile and unreachable results

- **Final plain check** (main 4842f898d): 5 ERROR lines, all left alone. The sweep's own errors are gone.
  - 4 FOREIGN Bowen–Chapman `.lean` artifact paths.
  - 1 in `leavitt-rooted-defect-window-carries-no-strict-design`, from lane gk3-leavitt-nonlinear, still running.
- **Stubbed compile** (clone only): placeholder `.lean` files, plus `requires` stripped from that one claim, gives
  exit 0: 12265 claims and 12424 routes compiled. 7078 of 24689 nodes are ESTABLISHED with `reachable: false`.
- **This session's nodes.** Commits carrying either trailer since 2026-09-12 touched 381 research ids. 154 of them
  are ESTABLISHED and unreachable; the list is in `research/artifacts/cairn-steward-2026-09-14-unreachable-established.txt`.
  No routes were invented to reconnect them.
- **Unreachable among the 78 claims and routes this sweep landed** (31, ESTABLISHED, serving no root):
  - `adian-lots-with-acyclic-initial-or-terminal-graph-are-dr`
  - `arzhantseva-steenbock-kazhdan-groups-without-unique-products`
  - `block-weight-matrix-test-lot-presentations-are-dr`
  - `centerless-fp-finitely-many-conjugacy-classes-gives-pbh`
  - `connes-embeddable-tracial-algebras-solve-nonsingular-equations`
  - `diagonal-cone-covered-actors-lie-in-binary-leavitt-unit-group`
  - `fp-simple-type-a-actions-iff-finite-bi-index-subgroups`
  - `fpbs-tree-projected-rigid-decorations-discrete-automorphisms`
  - `fully-residual-limits-preserve-trivial-idempotents`
  - `howie-locally-indicable-nonsingular-equations-are-solvable`
  - `injective-labeled-oriented-trees-are-aspherical`
  - `kazhdan-groups-without-unique-products-are-zero-divisor-hosts`
  - `kl-iff-acyclic-torus-amalgam-schur-injectivity`
  - `kl-yields-tracial-roots-for-quotient-indicator-traces`
  - `length15-16-free-piece-residue-classes-hyperbolic-special`
  - `linton-graph-certificate-for-free-magnus-pieces`
  - `lot-collapsed-maximal-sub-lot-test-transfers-asphericity`
  - `lot-disjoint-sub-lots-relatively-injective-transfer-asphericity`
  - `lot-reductions-preserve-homotopy-type`
  - `magnus-embedding-mod-m-into-wreath-product`
  - `no-free-subsemigroups-give-fg-kernels-over-ea-quotients`
  - `non-automorphic-hnn-extensions-contain-free-subsemigroups`
  - `nonsingular-coefficient-kernel-in-locally-indicable-residual`
  - `nonsingular-injectivity-passes-to-proper-power-relators`
  - `product-variety-free-groups-satisfy-permutational-boone-higman`
  - `proper-self-conjugate-subgroups-force-free-subsemigroups`
  - `q34-counterexample-necessary-conditions`
  - `residually-p-groups-have-trivial-idempotents-in-characteristic-p`
  - `root-extensions-descend-from-a-locally-universal-algebra`
  - `zero-divisor-host-is-not-virtually-compact-special`
  - `zero-one-coloring-test-implies-dr`
- **Duplicate warning naming a sweep node:** `no-free-subsemigroups-give-fg-kernels-over-ea-quotients`
  (solve-fp-intermediate-growth, landed ff757f44a) states the same theorem as
  `no-free-semigroup-ea-quotient-kernels-are-fg` (694acc5bc, session 01LwePEPxjENyat74TYf4oCw). It is a genuine
  duplicate, not a distinct claim. It needs a merge by the owners, and no `distinct_from` was added.
