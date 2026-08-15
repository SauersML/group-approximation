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

Eleven commands, no more:

```text
bin/cairn check [--changed]        compile + lint + duplicates; refreshes FRONTIER.md
bin/cairn preview                  research-state delta of working tree vs HEAD
bin/cairn frontier                 unresolved claims worth attacking, with locks
bin/cairn context <id> --budget N  one bounded packet: statement, derivation,
                                   routes in/out, reusable claims, dead space
bin/cairn search <q> [--notes]     lexical search over graph (and notes/)
bin/cairn impact <id>              what would change if this claim were established
bin/cairn lock <id> --ttl 45m      TTL work lock (re-run to extend) · unlock
bin/cairn next --lock              atomically select + lease a frontier claim
bin/cairn site                     static HTML site (human display is downstream)
bin/cairn telemetry                usage stats — the input for cutting more
```

Humans read `FRONTIER.md` (the generated home screen: status trees,
frontier, locks) rather than running commands.

Every query command takes `--json`; stable exit categories: `0` ok,
`2` duplicate candidates, `3` lease conflict, `4` invalid graph.

## Duplicates

`check --changed` refuses lookalike claims (exit 2). There is no `--force`;
if genuinely distinct, record why — the rationale is knowledge:

```yaml
distinct_from:
  outer-pvm-synchronization: that claim demands one joint PVM; this one ...
```

## Locks

TTL work locks (`owner / acquired_at / expires_at`; re-run `lock` to
extend) live under `.cairn/` — scheduler state, never committed into mathematical
history, never a frontmatter key. Filesystem backend today; the interface
is the contract, so a distributed backend can replace it without touching
the DSL. `CAIRN_AGENT` sets the default owner.

## Telemetry

Every invocation appends one record to `.cairn/telemetry.jsonl` (timestamp,
agent, command, argv, exit code, duration). `bin/cairn telemetry` summarizes
it: per-command usage and error rates, per-agent counts, exit-code
distribution, and commands never used — the empirical input for evolving
this design. Observability state like locks: never committed, never able to
affect research state.

## The agent loop

```text
bin/cairn next --lock --json        # find + lease work
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
