# Cairn — the research kernel (schema `rg: 2`)

A build system whose build targets are unknown facts: every finding is a
waymark stacked in unmapped terrain for whoever comes next.

> The framework itself is developed standalone at
> <https://github.com/SauersML/Cairn> (pip-installable and documented).
> This repo pins it as the `tools/cairn` submodule; `bin/cairn` runs it.
> After a fresh clone: `git submodule update --init tools/cairn`.
> To pick up upstream changes: `git submodule update --remote tools/cairn`
> and commit the new pin.

The kernel is deliberately tiny — **two objects, one extra relation**:

$$\boxed{\text{Claim}} \qquad \boxed{\text{Route: Claims}^* \Rightarrow \text{Claim}} \qquad \boxed{\text{established Claim invalidates Routes}}$$

Everything else falls out:

$$\operatorname{Solved}(Q) \;=\; \bigvee_{R \to Q} \; \bigwedge_{P \in \operatorname{requires}(R)} \operatorname{Solved}(P).$$

A **reduction** is a route with one prerequisite. An **equivalence** is two
routes, one each way. A **direct proof** is a route with `requires: []`.
An **obstruction** is an established claim that `invalidates:` routes.
None of these are object types; the compiler recognizes the patterns.

## Claim

A mathematical proposition. Unresolved → a hole (`sorry`); established → a
reusable theorem. **These are not different object types** — today's open
question is tomorrow's lemma. Status is always computed, never declared.

```markdown
---
rg: 2
id: same-orbit-closure
kind: claim
title: Same-orbit closure for the child translation images
---

On positive total trace, the two child translation images must remain
inside one source-sized paired orbit up to vanishing boundary leakage.
```

Optional keys: `root: true` (program-level target; frontier is computed
from roots), `invalidates: [route-ids]` (fires only once this claim is
ESTABLISHED), `distinct_from:` (see duplicates below), `artifacts: [...]`.

## Route

A justified implication `AND(requires) ⟹ target`. **Its existence asserts
the implication is valid** — it is a mathematical commitment, not
brainstorming; the body carries the argument.

```markdown
---
rg: 2
id: orbit-summed-extraction
kind: route
title: Orbit-summed whole-map extraction after same-orbit closure
target: common-self-map-law
requires: [same-orbit-closure, transition-equivariance]
---

## Why sufficient

Assuming same-orbit closure and transition equivariance, orbit-summing ...
```

`requires: []` asserts a **complete direct proof** of the target — never a
placeholder. If you cannot state the implication yet, write in `notes/`,
not here. A route discovered to be wrong is killed by an obstruction
claim's `invalidates:` — source-owned, so nobody edits the victim and
concurrent agents never contend.

## Canonical vs noncanonical

```text
research/*.md          claims + routes, one flat folder (`kind:` says which)
research/artifacts/    substantial proof artifacts routes may cite
notes/                 scratch, session logs, abandoned calculations
```

**If it can affect the authoritative graph, its justification lives in
authoritative space.** A route's body should justify its implication; large
arguments go in `research/artifacts/` (or a Lean module, or the docs/
proof corpus) and are cited via `artifacts:`. Citing `notes/` from a
canonical file is a lint **error** — notes are searchable, but they can
never change compiled research state. Ids are kebab-case slugs: the name
is the language (`same-orbit-closure`, not `Q-0010`).

The write path is your editor: **agents create and edit these files
directly with their normal tools.** Before committing, run
`bin/cairn check --changed` and `bin/cairn preview`.

## The CLI (read-only over canonical files)

It provides what a coding agent cannot get by editing Markdown:

Twelve commands, no more:

```text
bin/cairn check [--changed]        compile + lint + duplicates; refreshes
                                   FRONTIER.md   alias: build
bin/cairn preview                  research-state delta of working tree vs HEAD
bin/cairn status                   one screen: counts, goals, top frontier, claims
bin/cairn frontier                 unresolved claims worth attacking, with claims
bin/cairn why <id>                 derivation if established; why it matters if open
bin/cairn context <id> --budget N  one bounded packet: statement, derivation,
                                   routes in/out, reusable claims, dead space
bin/cairn search <q> [--notes]     lexical search; --similar ranks by similarity
                                   to an id or text   alias: relevant
bin/cairn impact <id>              what would change if this claim were established
bin/cairn lock <id> --ttl 45m      advisory TTL claim (identity-free) · unlock
bin/cairn site [--serve]           static HTML site (human display is downstream)
bin/cairn telemetry                usage stats — the input for cutting more
```

Humans read `FRONTIER.md` (the generated home screen: status trees,
frontier, claims) rather than running commands.

Every query command takes `--json` (errors included — a JSON envelope on
stdout); stable exit categories: `0` ok, `2` duplicate candidates,
`3` already claimed, `4` invalid graph, `64` usage error, `1` runtime
error. Unknown ids fail with nearest-id suggestions; lock TTLs require
an explicit unit.

## Duplicates

`check --changed` refuses lookalike claims (exit 2). There is no `--force`;
if genuinely distinct, record why — the rationale is knowledge:

```yaml
distinct_from:
  outer-pvm-synchronization: that claim demands one joint PVM; this one ...
```

## Claims (work locks)

Advisory, identity-free TTL claims live under `.cairn/` — scheduler
state, never committed into mathematical history, never a frontmatter
key. Everyone is one team: a claim means "someone is on this," each
worker knows which work is its own, `unlock` always works, and the TTL
cleans up after crashes. Filesystem backend today; the interface is the
contract, so a distributed backend can replace it without touching the
DSL.

## Telemetry

Every invocation appends one record to `.cairn/telemetry.jsonl`
(timestamp, command, argv, exit code, duration — no attribution).
`bin/cairn telemetry` summarizes it: per-command usage and error rates,
exit-code distribution, and commands never used — the empirical input
for evolving this design. Observability state like claims: never
committed, never able to affect research state.

## The agent loop

```text
bin/cairn status                    # goals, holes, what's claimed
bin/cairn lock <id> --ttl 45m       # claim an unclaimed hole
bin/cairn context <id> --budget 30000
bin/cairn search "..." / relevant <id>   # search before inventing
   ... do mathematics; write notes/ freely ...
$EDITOR research/<new-claim>.md research/<new-route>.md
bin/cairn check --changed && bin/cairn preview
git commit                          # durable provenance
bin/cairn unlock <id>
```

The discipline in one question: *is this a new proposition we must name
(Claim), a new sufficient implication between named propositions (Route),
or neither (notes/)?* A five-page failed exploration is notes, not a node.

## External reconnaissance and computational claims

Cairn's duplicate checker is deliberately repository-local.  Work on a named
problem from the outside literature therefore needs an **external gate** before
anything is promoted into the graph.  In particular, a promising search trace
or an independently rediscovered lemma is not yet a Cairn theorem.

Use the following discipline for external/open-problem work:

1. **Search this repository first.** Run lexical and similarity searches over
   canonical files and `--notes` before inventing a new statement.  The external
   problem may already be solved here under different language, or an attempted
   bridge may already be dead.
2. **Recheck problem status at the time of the attack.** For anything whose
   status could have changed, use a current authoritative problem page plus a
   primary source when available; record the exact date checked.  Do not inherit
   “open” or “solved” from an old benchmark list, cached snippet, or previous
   session summary.
3. **Audit novelty beyond theorem prose.** Search papers, appendices,
   supplementary files, and released source code.  An algorithmic reduction
   implemented in old code is prior art even if the paper's prose does not state
   it in the same words.
4. **State the certificate boundary exactly.** A positive finite construction
   should carry the explicit witness and an exact verifier.  A computational
   nonexistence result needs both a proof that the recursion/pruning is complete
   and a replayable *full* exhaustion.  A bounded-depth search, heuristic run,
   near-solution, or exhausted subfamily is evidence only; record its exact scope
   in `notes/`, never as a `requires: []` route.
5. **Keep graph relevance separate from mathematical interest.** If a sound
   external result has no honest implication to a root or reusable claim in this
   program, do not create an unrelated Cairn node merely to archive it.  Off-axis
   reconnaissance belongs in `notes/`; move substantial material into
   `research/artifacts/` only when it supports canonical research state (or a
   maintained canonical audit already serves that role).
6. **Correct aggressively.** If a freshness check or prior-art search overturns
   an earlier assessment, record the correction and withdraw the stronger claim.
   Provenance is more valuable than preserving a flattering narrative.

This is the computational analogue of `check --changed`: a route enters the
kernel only after both its mathematics **and its claim of novelty/status** have
survived the relevant checks.

## Semantics notes

- The fixpoint is least: cycles never self-justify (cycle lint warns).
- Invalidation activates only when the invalidating claim is ESTABLISHED;
  a non-stratified establishment/invalidation loop is a build error.
- Killing every route into a claim leaves it OPEN, not disproved — proving
  impossibility means establishing the negation as its own claim and
  saying so in prose; the kernel only understands implications.
- Literature imports are direct-proof routes whose body/artifact cites the
  source — grep `requires: \[\]` for the full trust surface of the graph.

## Legacy corpus

`docs/TRUE_*` / `FALSE_*` stay where they are: they are the proof corpus,
cited via `artifacts:`. Migration happens by *proposing* claims/routes for
review, never by bulk conversion.
