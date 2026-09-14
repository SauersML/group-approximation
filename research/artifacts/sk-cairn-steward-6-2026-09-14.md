# sk-cairn-steward-6: MSI Cairn reachability check for the sk swarm (2026-09-14)

User order: "make sure everything is in Cairn". This lane runs ONE full `tools/cairn.py check` on MSI at the current main tip and reports every sk id that does not reach a root.

## Method
- Script: steward-3/5's `cc-msi.sh`, copied to `/scratch.global/sauer354/sk/steward6/` with its paths rewritten (0 references to steward3 left).
  - It takes a `git archive` of main into a clean workspace and applies workspace-only stubs for known peer errors, and for ids over 64 characters.
  - It runs `cairn.py check` under `timeout 1500`, then reads `.cairn/cache/graph.json` and prints `UNREACH <kind> <status> <id>` for every scoped id without `reachable`.
- Launched detached (nohup setsid) at 11:13:21 CDT. Local calls were single ssh waits of at most 520 s; no local loop and no local background probe.
- Scope: 710 ids. That is the 705 in steward-3/5's `sk-ids.txt`, plus every `research/<id>.md` landed through `$SK2/landed.log` (112 ids, all present at the tip). New to the scope:
  - `discrete-kazhdan-groups-are-finitely-generated`
  - `orbitwise-gap-sofic-approximations-are-local-embeddings`
  - `orbitwise-gap-sofic-approximations-local-embeddings-proof`
  - `singer-identities-make-subshift-el3-isos-standard`
  - `singer-identities-make-subshift-el3-isos-standard-proof`

## Peer compile blocker from steward-5's run
- steward-5's check at 85fdee4bbf failed with EXIT=4: `ERROR: research/leavitt-rooted-defect-window-carries-no-strict-design.md: unknown keys for claim: ['requires']`. That node belongs to a peer lane.
- The fix 0b43ab3fc ("Move the rooted defect window derivation into a route node") is an ancestor of the tip. At the tip the node's front matter has no `requires` key. This lane edited no peer node.

## Result: the check compiles and passes
- `TIP=7de7861fa094cbca50c3e66390974ae692efe616`: `EXIT=0 SECS=963`, 0 `ERROR` lines, "compiled 12293 claims + 12448 routes -> .cairn/cache/graph.json". The graph cache was written at 11:42 CDT.
- No long-id or Kervaire stubs were needed (`LONG_ID_STUBS 0`, `KERVAIRE_STUBBED=0`).
- Scope: 710 sk ids. Reachable: 698. Not reachable or missing: 12, listed below.

### Dead space (11 ids, all justified, no action)
Refuted claims kept as firewalls. Each records a false statement so that it is never used again.
- `double-swap-embeds-group-in-derived-subgroup` (FAIL by sk-verify-4; on the rules' list of false maps)
- `subshift-el3-isomorphisms-recognize-diagonal-subgroups` (refuted: inn(diag(u,1,1)) is outer)
- `elementary-group-lef-growth-separates-subshifts`
- `every-lef-group-embeds-in-a-z-subshift-elementary-group`

Invalidated routes, kept as recorded dead ends:
- `double-swap-embeds-group-in-derived-subgroup-proof`
- `amenable-groups-embed-in-simple-kazhdan-linear-sofic-proof`
- `free-minimal-sft-el-sofic-via-subshift-marked-limits`

Stale ids with no file on main. They come from pre-reboot scope lists; the nodes were renamed or superseded, and nothing on main references them.
- `subshift-elementary-group-simple-iff-minimal`
- `subshift-elementary-group-simple-iff-minimal-proof`
- `wilson-countable-rf-embeds-in-2-generator-rf`
- `wilson-countable-rf-embeds-in-2-generator-rf-citation`

This matches the dead-space list of the last full check (09:07, tip c95771958a) exactly.

### A live sk finding that did not reach a root (1 id)
- `discrete-kazhdan-groups-are-finitely-generated` (claim, ESTABLISHED). sk-verify-23 landed it at b9b3a8c7b1, 11:09 CDT, after the last wiring pass. It is new to the scope.

## Wiring
- `crossed-product-el-kazhdan-iff-finite-field-and-subshift-proof` (reviewed by sk-verify-5) uses exactly this fact in step (3 ⇒ 2), "a locally compact group with property (T) is compactly generated". Before the merge that step cited only "theorem number not re-verified here".
- Merged onto main's blob 4be1647969: `requires: [elementary-groups-over-fg-rings-have-property-t, discrete-kazhdan-groups-are-finitely-generated]`. Step (3 ⇒ 2) now cites the node and BHV Theorem 1.3.1, whose locator sk-verify-23 read at source.
- No other text changed. The route's target is reachable, so the claim now has a path to a root.
- Landed together with this artifact via skland2.sh; the commit SHA is in the lane's final report.
- A re-check on MSI was launched after the landing; its outcome is in the final report.

## Peer notes (no action)
- `research/fpbs-kazhdan-groups-have-cost-one.md` and `research/fpbs-kazhdan-positive-rank-gradient.md` mention the id in text but are not sk nodes, so this lane left them alone.
