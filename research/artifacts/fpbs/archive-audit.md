# Audit of the supplied Cairn snapshot

Source: `group-approximation-main (31).zip`.
Archive entries: 23783.
SHA-256: `a804ac54313522f069b43ff6876547f8c7b8a16e552e5a2b4ff14564897eba4e`.

## Search and reading scope

The ZIP was inspected through the local filesystem; the conversation-file
search index returned no parsed result for it. Searches used the target names
and the terms fixed price, percolation, cost-one, and treeable. No filename
matched `fixed.?price|benjamini|schramm|percolation` (0 matches).
No dedicated proof of either universal target was located. This is a search
finding, not a claim to have independently verified every argument in the
roughly fifteen-thousand-node research graph.

The relevant source excerpts are retained verbatim under `source_excerpts/`.
Their per-file hashes are in `research/artifacts/source-manifest.json`.

## Most relevant existing progress

`notes/TRUE_ROUTED_HOLONOMY_PHASE_REPAIR.md`, Section 1 (lines 5–38), records
that cost one alone does not bound the product of routing width and normalized
tree excess. It explicitly withdraws the earlier unconditional compact-skew
permanence shortcut. The retained result additionally requires phase-compatible
routes. The new reciprocal-distance example and compactness lemma address
this cost-versus-route issue; they do not refute the corrected conditional
phase theorem.

`research/non-ce-relation-is-not-treeable.md` is a non-treeability claim, with
its cited proof route in `research/non-ce-relation-not-treeable-proof.md`.
The stabilizer-realizing free-group action in that node is not a free action
in the Fixed Price sense. A non-treeability obstruction does not compare the
infima of graphing costs of two free actions of the same group. This audit
uses that distinction, not an independent certification of the whole
operator-algebraic dependency chain.

`research/sl2-homogeneous-action-is-not-treeable.md` supplies a further
non-treeability claim. It is retained for context but not used as a premise
of the new percolation inequality.

## Original check versus the isolated addition

Running the supplied `tools/cairn.py check --json` against the extracted
original snapshot returned status `invalid`, process exit code
4, 7414 parsed claims, 7575
parsed routes, and 31 errors (54 total findings).
The full output is `research/artifacts/original-cairn-baseline.json`.
One error is a claim identifier longer than the accepted slug length. Others
include artifact references pinned to historical git revisions unavailable
in this ZIP snapshot. These are not repaired or concealed by the addition.

The isolated addition's `cairn-check.json` has status `ok` and no findings:
10 claims, 8 routes, 7 claims marked ESTABLISHED by their written/cited routes.
Both universal goals and the fixed-price-one percolation kernel remain OPEN.
See the saved goal-status JSON files. Cairn's dependency compilation is not
Lean proof verification and does not certify a mathematical claim merely by
accepting its node.

The vendored Cairn script and the required math CSS/JavaScript assets are
byte-identical copies from the supplied archive. Their hashes are included.
The original uploaded ZIP and the original canonical research nodes are
unchanged by this package.
