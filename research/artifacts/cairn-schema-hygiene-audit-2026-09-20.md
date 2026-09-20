# Schema hygiene audit and conservative source repair

Date: 2026-09-20. The initial read-only audit is preserved below. A
subsequent authorized structural repair is recorded at the end; it
creates no accepted mathematical route and promotes no claim.

`bin/cairn check --json` reports 70 errors: 57 unknown-key errors,
7 invalid `distinct_from` entries, 3 missing `requires`, and 3 missing
targets. These affect 64 canonical files. The CLI correctly refuses
compilation and leaves derived outputs untouched.

## Critical false-acceptance witness

`research/fix-classtransposition-presentation.md` is a build-status note
encoded as a route. It has a valid target,
`class-transposition-relations-present-ct-p-z`, an illegal `status: OPEN`,
and **no `requires` field**. Its body explicitly describes unprobed
modules and outstanding mathematical/formal obligations.

In `tools/cairn.py`, `Node.get_list` maps a missing list to `[]`.
`Graph.compile` passes that list to `route_requires`, and `_solve`
tests `all(...)`. Consequently the in-memory graph marks this malformed
route COMPLETE and its target ESTABLISHED, despite the schema error.
It is the target's **only incoming route** in the audited snapshot.

A read-only in-memory comparison removed these four malformed routes:

```
fix-classtransposition-presentation
fix-nmn-tww-extension-absorb-quasicentral-step
fix-nmn-tww-std-operator-algebra-complete
nm-exclusive-pocket-first-turns
```

Exactly one surviving node changed derived status:

```
class-transposition-relations-present-ct-p-z: ESTABLISHED -> OPEN
```

No downstream claim or surviving route changed status, and no canonical
`requires`, `invalidates`, `refuted_by`, or `target` relation references
the four removed route ids. The last id does occur in an invalid
`distinct_from` declaration, addressed below. These observations concern
the audited working-tree snapshot, not a claim that future graph changes
cannot add consumers.

Therefore cleaning the whole graph while preserving **every** current
in-memory derived status is not a sound objective: one status is already
an artifact of malformed input. Do not add `requires: []` to preserve
it. A separate proof review would be needed to establish that target.

There is a related kernel hazard: `Graph.compile` filters unknown or
wrong-kind prerequisite ids out of route prerequisites. Thus a malformed
route with unresolved premises could likewise acquire an empty or weaker
premise list. A future kernel guard should make malformed routes
ineligible for proof propagation rather than merely rely on callers to
inspect lint errors. This audit makes no kernel change.

## Exact structural classifications

### 54 claim-level dependency lists: 146 declared prerequisites

All 54 unknown `requires` fields on claims contain nonempty lists; all
146 listed ids resolve to existing claims. **None** of the 54 claims
has any incoming paired route, with matching or different premises.
All 54 currently derive OPEN. Claim-level `requires` is ignored by the
solver, so moving each list verbatim into explicitly historical prose
would preserve the current actual proof graph and derived statuses.

However, these lists clearly record intended dependencies that are not
currently represented by valid routes. Creating paired routes would
assert mathematical implications and is not a schema-only repair.
They need individual mathematical review under `research/README.md`'s
rule against bulk migration. There is no paired-route coverage that
would justify silently deleting the declarations. No lists were moved.

### Four malformed route-shaped documents

- `fix-classtransposition-presentation`: build log with target but no
  premises, plus illegal status; causes the false acceptance above.
- `fix-nmn-tww-extension-absorb-quasicentral-step`: resolved build log,
  illegal status, no target, no premises. Cannot establish a claim.
- `fix-nmn-tww-std-operator-algebra-complete`: same classification.
- `nm-exclusive-pocket-first-turns`: substantial mathematical argument
  with `requires: []` but no target, and prose describing an OPEN route.
  It cannot establish a claim as encoded. Choosing a target or deciding
  its proof is complete is a mathematical decision, not formatting.

The three `fix-*` files naturally belong in the notes tier, preserving
their full contents and provenance. The last can also be preserved as
a note pending review; it must not be made a claim or assigned a target
merely to silence validation. No document was moved.

### Seven `distinct_from` entries in six files

Every alleged “unknown claim” is actually an existing **route**, not a
missing identifier. These are route-review descriptions misencoded as
claim distinctness metadata:

| Source claim | Referenced route |
| --- | --- |
| `bartholdi-mitrofanov-proposition-2-4-gap-and-repair` | `nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups` |
| `birget-question-via-decidable-bartholdi-mitrofanov-hosts` | `nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups` |
| `hyperbolic-racgs-min-star-order-review` | `hyperbolic-racgs-contracting-rsg-via-min-star-order` |
| `hyperbolic-racgs-min-star-order-review` | `hyperbolic-racgs-with-spread-nerves-contracting-rsg-proof` |
| `kourovka-19-46-subshift-route-review` | `ct-z-periodic-groups-via-subshift-factors-of-elements` |
| `nm-exclusive-pocket-first-turns-review` | `nm-exclusive-pocket-first-turns` |
| `typed-core-backward-half-review` | `hyperbolic-racgs-contracting-rsg-via-min-star-order` |

Moving the exact descriptions into a “Route under review” prose section
would not change mathematical proof propagation. Automatically replacing
each route id by its target would alter the meaning of the descriptions
and, for the targetless exclusive-pocket document, is impossible.

## Smallest safe direction, not an executed migration

The 54 misplaced lists and 7 route-review annotations can be preserved
verbatim in prose without changing the proof graph. Preserve the four
malformed documents as notes rather than inventing premises, targets,
or proof acceptance. This would remove the 70 listed schema errors but
must correctly downgrade the one false acceptance, and should be
performed as explicitly reviewed structural cleanup, not as mathematical
bulk migration. Warnings and graph reachability are separate work.

At the parent's request, no cleanup was executed: the current global
graph remains invalid, and the false-acceptance witness is recorded for
an explicit correction and a later kernel-guard review.

## Subsequent authorized repair, 2026-09-20

After the fail-closed kernel correction, the parent authorized the
following source-only cleanup. The preceding findings describe the
pre-repair snapshot, including the erroneous acceptance under the old
kernel; they are not a claim that the current kernel accepts it.

1. All 54 rejected claim-level `requires` lists were moved verbatim,
   including all 146 prerequisite ids in their original order, into
   fenced YAML under **Proposed dependency record (not an accepted
   route)** in the same files. The new text explicitly states that
   individual mathematical review is required before any route is
   accepted. All historical mathematical prose is retained. No paired
   route was created.
2. The seven route-valued `distinct_from` entries in the six files
   listed above were moved into **Route comparison record** prose,
   preserving their comparison text and supplying actual links. All
   valid claim-valued entries remain in metadata. The exclusive-pocket
   comparison links to its archived note rather than inventing a claim.
3. The four malformed route-shaped documents were moved byte-for-byte
   by `apply_patch` into the notes tier, retaining their complete
   original frontmatter and bodies for provenance. They are no longer
   canonical nodes. No `requires`, target, claim, or proof acceptance
   was invented for any of them.

| Former canonical path | Preserved note path | Why it is not an accepted mathematical route |
| --- | --- | --- |
| `research/fix-classtransposition-presentation.md` | [notes/cairn-schema-pending/fix-classtransposition-presentation.md](../../notes/cairn-schema-pending/fix-classtransposition-presentation.md) | Unprobed build-status record; missing premises must not become an empty-premise proof. |
| `research/fix-nmn-tww-extension-absorb-quasicentral-step.md` | [notes/cairn-schema-pending/fix-nmn-tww-extension-absorb-quasicentral-step.md](../../notes/cairn-schema-pending/fix-nmn-tww-extension-absorb-quasicentral-step.md) | Resolved build-status record, with no mathematical target or premises. |
| `research/fix-nmn-tww-std-operator-algebra-complete.md` | [notes/cairn-schema-pending/fix-nmn-tww-std-operator-algebra-complete.md](../../notes/cairn-schema-pending/fix-nmn-tww-std-operator-algebra-complete.md) | Resolved build-status record, with no mathematical target or premises. |
| `research/nm-exclusive-pocket-first-turns.md` | [notes/cairn-schema-pending/nm-exclusive-pocket-first-turns.md](../../notes/cairn-schema-pending/nm-exclusive-pocket-first-turns.md) | Targetless argument described as OPEN; deciding its target and acceptance requires individual review. |

Read-only reference search found no active canonical `artifacts` entry
pointing to the four former paths. Historical diagnostic snapshots and
the initial audit retain the old paths as historical evidence; the live
review link was updated to the note path. All four documents remain
recoverable in full at their new paths, in addition to version history.

No local Python, Cairn command, build, or test was run during this
repair. Validation is delegated to the MSI workflow: compare all
surviving derived statuses under the same fail-closed kernel, excluding
only the four archived route ids, and verify that the false
`class-transposition-relations-present-ct-p-z` acceptance remains OPEN.
The status comparison and final schema result are pending that remote
validation; the structural edits alone are not presented as a test pass.
