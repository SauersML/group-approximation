# sk-rigidity-merge: the rigidity theorem for G_X merged into Cairn (2026-09-14)

Lane sk-rigidity-merge. It merges two independent reviews of sk-orthogonality-o's rigidity result and establishes it in
the graph:
- sk-verify-25b (5affb84500), adversarial: fixes A1–A3 and C1–C4;
- sk-verify-25a (248bd5cc91), line by line: fixes W1–W5.

Base tip c82290e0d1. No new mathematics: every change is a verbatim fix from those reviews, a status update, or wiring.

## Result now established

Let `X, Y` be infinite minimal subshifts, `R_X = LC(X,F_2)⋊Z` and `G_X = EL_3(R_X)`. Every isomorphism `α: G_X → G_Y`
equals `inn(k)∘M_3(φ)|_{G_X}`, possibly after the graph automorphism `γ_X`, for some `k ∈ GL_3(R_Y)` and a ring isomorphism
`φ: R_X → R_Y`. So `G_X ≅ G_Y ⇒ R_X ≅ R_Y ⇒` X and Y are strongly orbit equivalent.
- `subshift-el3-isomorphisms-are-standard-over-f2`: OPEN → ESTABLISHED through the new route
  `subshift-el3-isomorphisms-are-standard-over-f2-proof`, which requires `frobenius-bicommutants-make-subshift-el3-isos-standard`.
- `subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence`: OPEN → ESTABLISHED, because its existing route
  `subshift-el3-f2-iso-soe-via-standard-isomorphisms` is now complete.

## Fixes merged, and where

| Fix | Source | Merged into |
|---|---|---|
| A1, W1, C1 (status lines) | 25b §2–3, 25a §5 | both claim nodes; artifact part 1 header and §0, part 2 header |
| A2 (Step 5 without Proposition F item 2) | 25b §2 | part 1 §3 Step 5; Singer route step 4 |
| A3 (restriction to F21 semisimple) | 25b §2 | part 1 §3 Step 2; Singer route step 3 |
| W2 (Step 6 bicommutant) | 25a §5 | part 1 §3 Step 6; Singer route step 5 |
| W3 (Step 7 gives φ: R_X → R_Y) | 25a §5 | part 1 §3 Step 7 and Theorem A statement; Singer claim and route; Theorem D |
| W5 (Proposition F numbering) | 25a §5 | part 1 §3 Step 4; Singer route step 4 |
| C2 (corner centre, no corner isomorphism) | 25b §3 | part 2 header and Lemma X; Frobenius claim status; route step 2 |
| C3 (g_t(a) in F_2I + span K_V) | 25b §3 | part 2 Theorem C proof; route step 3 |
| C4 (scope; unused `requires`) | 25b §3 | part 2 §4 scope paragraph; Frobenius claim; `diagonal-recognition-makes-subshift-el3-isos-standard` dropped from the Frobenius route's `requires` |
| W4 (orientation after γ_X) | 25a §5 | part 2 Theorem D proof; Frobenius route step 7 |

Locator correction: C4's source text says "§4" of the note. The Questions section is §5 of rev4.5, so the merged text
says "Questions section".

## Other status updates and wiring

- `subshift-gl3-index-kernel-is-elementary-group`: status line "ESTABLISHED (unreviewed)" → "ESTABLISHED (reviewed:
  sk-verify-18 PASS, part6)".
- Rigidity theme (`simple-kazhdan-lef-program-rigidity-results-assembly`): added
  `frobenius-bicommutants-make-subshift-el3-isos-standard`, `subshift-el3-isomorphisms-are-standard-over-f2` and
  `subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence`.
- Open problems (`simple-kazhdan-lef-program-open-problems-conjunction`): added the NEW open node
  `subshift-el3-group-isomorphism-forces-flip-conjugacy` and the existing `subshift-group-factors-determine-subshift-groups`.
  - The directive said to move `subshift-el3-isomorphisms-are-standard-over-f2` out of that conjunction, but it was
    never listed there. It was reachable only from the note's open-questions root, through
    `subshift-el3-f2-iso-soe-via-standard-isomorphisms`.
- Part 1 §4 (Theorem B, Lemma N, Corollary B′) and §5 are marked unreviewed and superseded by Theorem C, off the chain.

## Not done (main's decisions)

- Note root untouched, as directed.
- The note's open-questions conjunction `simple-kazhdan-lef-note-open-questions-conjunction` still lists
  `subshift-el3-f2-isomorphism-forces-strong-orbit-equivalence`, which is now established. That route belongs to the
  note root, so it was left alone; it should change only if the tex changes.
- `subshift-el3-isomorphisms-recognize-diagonals-up-to-normalizer` (Rec′), listed among the open problems: part 2
  claims it follows too, but neither reviewer examined (Rec′) separately, so it stays open here.
- No MSI `cairn check` was run by this lane.
