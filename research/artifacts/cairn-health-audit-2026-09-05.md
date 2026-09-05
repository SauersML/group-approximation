# Cairn source-graph health audit, September 5

The latest snapshot, including low-energy Schreier frames, the bounded
Gram second-moment corner theorem, and the nonuniform positive-corner
bootstrap, passes with **14,136 nodes and no errors, warnings, or duplicate
candidates** in 9.981 seconds. Comparison with the pinned commit
`027c44cb7bc59d699273153feff5871f628720ff` finds no newly dead claims,
newly detached lane tops, or new open claims lacking attempts. Its record
is `research/artifacts/spectral-corner-cairn-validation-2026-09-05.json`.
The integrated conditional Schreier theorem is established; SL5 flexible
stability and nonhyperlinear existence remain open. All seven edited
theorem, root, and proof-artifact files were compared byte for byte with
the validated archive after the check.

The preceding snapshot, including the explicit universal congruence host and
sublinear exact seeds, passes with **14,134 nodes and no errors, warnings,
or duplicate candidates** in 9.878 seconds. Comparison with the same pinned
commit `027c44cb7bc59d699273153feff5871f628720ff` also finds no newly dead
claims, newly detached lane tops, or new open claims lacking attempts.
Its record is
`research/artifacts/universal-schreier-host-cairn-validation-2026-09-05.json`.

The preceding snapshot, including the arbitrary-depth Leavitt equivalence and
rectangular seed alignment bound, passes with **14,130 nodes and no errors,
warnings, or duplicate candidates** in 12.058 seconds. Comparison with pinned
commit `027c44cb7bc59d699273153feff5871f628720ff` (14,128 nodes) also finds
no newly dead claims, newly detached lane tops, or new open claims lacking
recorded attempts. Its record is
`research/artifacts/depth-equivalence-seed-alignment-cairn-validation-2026-09-05.json`.

The preceding snapshot, including rectangular Schreier correction and the exact
two-depth overlap audit, passes with **14,126 nodes and no errors, warnings,
or duplicate candidates** in 10.888 seconds. It also compares against pinned
commit `47e34ed2f54d4b41007ae40cf4bae1ef7ac54da3` (14,124 nodes): there
are no newly dead claims, newly detached lane tops, or new open claims
missing recorded attempts. Its record is
`research/artifacts/rectangular-overlap-cairn-validation-2026-09-05.json`.

The preceding follow-up snapshot, including the flexible-dilation and mixed-depth
audits, passes with **14,120 nodes and no errors, warnings, or duplicate
candidates** in 9.342 seconds. Its record is
`research/artifacts/flexible-dilation-cairn-validation-2026-09-05.json`.

The preceding snapshot, including the small-angle curvature theorem,
passes with **14,108 nodes and no errors, warnings, or duplicate candidates**
in 8.755 seconds. Its record is
`research/artifacts/quadratic-curvature-cairn-validation-2026-09-05.json`.
The checker source matched the archived local source byte for byte.

The initial repaired source snapshot passed Cairn's native document validation,
reference and artifact lint, graph compilation, and unfiltered duplicate
scan: **14,102 nodes, no errors, no warnings, no duplicate candidates**.
The remote check took 8.328 seconds. The machine-readable record is
`research/artifacts/cairn-full-health-2026-09-05.json`.

This is graph validation, not mathematical proof-kernel verification.
`non-hyperlinear-group` remains `OPEN`. Open claims, refuted approaches,
and historical detached research lanes remain visible in derived state;
none was relabeled as proved or promoted to a root to make the check pass.

## Repairs

- Replaced the Mikhailova one-color proof's circular frontier dependency
  with the foundational GKP chart theorem actually used in its argument.
- Corrected invalid proof-node schemas, shortened three overlong IDs,
  and updated their real incoming references without compatibility aliases.
- Reconstructed missing claim statements from their surviving current
  proofs and repaired references to current extraspecial and packet lemmas.
- Made the five-Clifford finite packet verification explicit where deleted
  predecessors had previously been cited.
- Pinned three absent proof artifacts to verified historical Git objects.
  No working files were restored from Git.
- Recorded substantive distinctions for the Bost/determinant,
  countable/directed hereditary continuity, and countable/transfinite
  filtration pairs reported by the duplicate detector.
- Corrected a cycle-checker bug: a genuine two-way implication remains an
  equivalence after its endpoints have been proved. An unproved extra
  side condition still produces a cycle warning.

## Check execution and performance

All Python execution took place on MSI acn116, one short process at a
time. Source was read from a transferred snapshot of the local worktree,
including uncommitted nodes. Cairn's own `load_nodes`, `lint_nodes`,
`Graph`, and `duplicate_findings` functions checked the complete node set.
The workspace path manifest supplied artifact-existence information, and
the remote Git object database verified the historical pins. Snapshot
membership was checked against that manifest. The JSON records the source
archive digest; a detailed per-node digest inventory is retained in the
remote `.cairn/cairn-full-health-current-2026-09-05.json`.

The first scan found 28 structural errors, one additional cycle warning,
and three duplicate candidates beyond the already identified Mikhailova
cycles. Later scans also caught two newly written `kind: proof` nodes.
The final scan found none of these issues.

Cairn now compares with a pinned HEAD entirely in memory. It reuses
independent copies of unchanged parsed nodes and batch-reads changed
historical documents, preserving all document and reference validation.
It no longer creates thousands of scratch source files or skips comparison
when more than 200 nodes change. Rename detection includes both node IDs.
The checker version is `2.13.1`, invalidating cached old diagnostics.

Regression coverage includes independent derived node state, additions,
deletions, renames, more than 200 changes, malformed historical sources,
source changes during comparison, missing historical blobs, and genuine
versus conditional two-way implications, and source reuse after policy-only
findings. All 12 distinct regression cases passed remotely. Test repositories use `main`
and live on project storage, not RAM-backed temporary directories.
