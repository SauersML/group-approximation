# Coordinating agents on big solves: playbook (2026-09-17)

Written after the September swarms: a 240-agent wave and a solo follow-up. The orchestrator, meaning the session
that launches and lands the work, should read all of it. Workers only need the worker contract in Section 6.

Second revision (same day) adds tooling:

- a live coordination bus, `bin/cairn-live`;
- a paradigm engine that computes which *kinds* of attack are saturated, dying or never tried;
- pull-based self-dispatch;
- a serialized lander, `tools/cairn-land.sh`;
- five paradigm lanes for the Gottschalk cone (Section 11).

## 0. What the last swarm taught

| What happened | Cost | Rule it became |
|---|---|---|
| Shallow clone, and HEAD 61 commits behind a separate landing worktree | Checker errors that looked real | Section 1 pre-flight |
| Verifier stages died in a model outage after their solvers finished | 1,077 files and ~170 established claims sat uncommitted until a salvage pass | Land continuously (Section 7), keep a salvage step (Section 9) |
| 30 "high-impact" workflows went straight at flagship conjectures | One partial artifact, not landed | Decompose before solving (Section 4) |
| 60 targets × (solver + referee) | 4 Zaremsky resolutions and many attempts, all checked by agents only | Fewer, deeper lanes; say what verified each result (Section 8) |
| Node ids over 64 characters, stale artifact paths | `cairn check` exit 4 at landing | The worker contract lints before handing off (Section 6) |
| "Never landed" reported for work that was actually on main | A wrong report to the user | Check `git log origin/main` before saying anything about landing |
| Workers only saw the graph as it was at launch | Two agents re-derived one lemma, and one retried an approach another had just killed | Live bus: leases on *approaches*, a feed, dead ends posted at once (Section 2) |
| Every lane used the same few methods (entropy, local designs, sofic counting) | Many attempts, one shape of failure | Paradigm engine and roles (Section 3) |

## 1. Pre-flight (orchestrator, solo, before any agent)

```sh
git rev-parse --is-shallow-repository   # must be false, else: git fetch --unshallow
git fetch origin main && git status -sb  # clean tree, HEAD == origin/main
bin/cairn check; echo $?                 # must be 0 (warnings are fine)
bin/cairn status                         # goals, frontier size, active locks
python3 -m unittest tools/test_cairn_live.py   # the bus: 10 tests, <1 s
bin/cairn-live atlas <goal>              # which families are HOT, dying, COLD
```

Fix any exit-4 error before launching. Otherwise every worker inherits it and hands back a red graph.

## 2. The live bus: real-time sync and sharing

`bin/cairn-live` (implementation `tools/cairn_live.py`, stdlib plus the vendored `cairn` library) is an append-only
event log. The log is a JSONL G-Set:

- every event has a random id;
- state (leases, needs, lemmas, dead ends, sparks) is *folded* from the log;
- merging two logs is a union by id.

So the bus has no server, no locking protocol beyond an `flock` on append, and no merge conflicts. A torn last line
is skipped.

**Where it lives.** The default is `<cairn shared dir>/live/`, which every worktree of this repository in one
container shares. Workflow agents with `isolation: 'worktree'` therefore see each other's events at once.
Environment:

- `CAIRN_AGENT`: required for claim, heartbeat, release and dead. A missing agent exits 64, because leases are
  matched by agent.
- `CAIRN_WAVE`: namespaces one run. Default `default`.
- `CAIRN_LIVE`: overrides the directory (the tests use a temp dir).

**Leases are on approaches, not nodes.** `cairn lock` says "someone is on node X". A lease says "someone is attacking
X *by this idea*", so several agents can attack one hole in genuinely different ways:

```sh
bin/cairn-live claim <node> --family entropy-measure --sig "biased bernoulli count raising" \
  --intent "compute h^Rok of the 1/3-biased shift under psi"      # exit 0 granted, exit 3 blocked
```

A claim passes a **diversity rule**, checked against live leases and recorded dead ends on that node:

- **Same idea** is always blocked. That means signature token Jaccard ≥ 0.6, regardless of family.
- **A recorded dead idea** needs `--revive "<what is new>"`.
- **The same family** as a live lease needs `--same-family "<why this is different>"`.
- `--adopt <spark id>` takes over an idea someone posted and did not pursue, and closes the spark.
- `--new` allows a node that does not exist yet.

The claim is atomic: 16 forked concurrent claims admit exactly one.

**Heartbeat contract.** A lease has a TTL (default 4h). Run `bin/cairn-live heartbeat --node <id> --text "<progress
in one line>"` at least every hour; the progress line shows on the board. A lease that is not refreshed expires,
and its approach is free again.

**Posting.** Every post is one line of text:

| Command | Meaning | Side effect |
|---|---|---|
| `lemma <node> --text ... --files ...` | an established intermediate result, usable by others | posts transfer targets, meaning similar open nodes where it may also apply |
| `need <node> --text ...` | "I would finish if someone proved this" | carries a bounty: 1 + the number of claims it would newly establish |
| `dead <node> --text "<where it dies>"` | the approach failed | releases the lease and blocks that idea for everyone without `--revive` |
| `release <node>` | done, or dropped without a verdict | frees the approach |
| `spark --text ...` | an idea you will not pursue | others `--adopt` it |
| `question` / `answer --ref <id>` | a cross-lane question | |
| `verdict <node> --outcome refuted\|survives` | a referee result | |
| `landed <node>` | posted by the lander | |

Shorthand posts take a positional node or `--node`, and `--keywords` for transfer matching.

**Reading.**

- `feed --new`: everything since this agent's cursor, skipping its own events.
- `feed --cone <goal>`: only events near a goal. `feed --follow` streams.
- `board`: active leases with progress, needs by bounty, recent lemmas, dead approaches.
- `approaches <node>`: every approach to one node, both graph attempts and live leases.

**Across containers.** `bin/cairn-live sync` unions the log with a git ref, by default `refs/cairn-live/<wave>`, on
a remote. It commits the JSONL as a blob, retries on a lost race, and skips the push when nothing changed.
`--pull-only` only reads. **Pushing a sync ref to `origin` needs the user's permission.** Within one container no
sync is needed. `export FILE` / `import FILE` do the same by hand.

## 3. The paradigm engine: making agents think differently

The failure mode of the last swarms was not a lack of effort but a monoculture of method. The engine makes method
choice a computed, coordinated quantity.

**Families.** `tools/cairn_live_paradigms.json` lists ~17 approach families: finite models, entropy-measure,
operator algebras, group rings, linear characteristic, local designs, census computation, host geometry,
logic-computability, cohomology-index, symbolic dynamics, probability, stability, calibration,
minimal-counterexample, reframing, quantifier-shift. Each family is recognised by keyword regexes over node text.
Agents add families at run time with `bin/cairn-live family add NAME --text "<gist>" --keywords "<regex>,<regex>"`; fold the useful ones
back into the file.

**Atlas.** `bin/cairn-live atlas <goal>` tags every node in the goal's neighbourhood (cone plus similar nodes) by
family and reports, per family:

- established, open, attempts and dead attempts nearby;
- live leases;
- temperature:
  - **HOT** if its nearby work is at or above the 75th percentile;
  - **COLD** if its representation is below 0.35 while it has at least 20 established claims graph-wide.
    Representation is its share of work here divided by its share of established work graph-wide.

COLD means a mature toolbox exists in the graph and has almost never been pointed at this goal. On the Gottschalk
goal (cone 89 nodes, neighbourhood 156, 39 open holes) the COLD families are operator-algebras (rep 0.25) and
stability-approximation (0.14). Entropy-measure and local-designs are HOT.

**Roles.** A role is a way of thinking, not a topic. `bin/cairn-live card <role> <goal> [--node <hole>]` prints a
brief built from the live graph: the role's instruction, the relevant families (COLD for a transplanter, HOT for a
heretic), dead attempts to mine, calibration counterexamples, and for `--node` the hole's status, bounty, attempt
headings and live leases.

| Role | Instruction in one line |
|---|---|
| inverter | write the biography of a minimal counterexample; contradict it or turn it into a construction recipe |
| transplanter | import a COLD family's central tool, write the dictionary, prove the easiest translated case or find where it breaks |
| obstruction-miner | find the one invariant most dead approaches hit; kill the class or find the gate that changes it |
| reframer | change the objects (groupoids, relations, channels, vector alphabets), prove it there, isolate the transfer |
| scale-shifter | change the quantifier level (one tester host, all large alphabets, generic groups, arithmetic form) |
| compute-scout | search a region no census covered; report anomalies with runnable scripts |
| heretic | name three unstated assumptions shared by the HOT families; deny each in turn |
| calibrator | name the calibration counterexamples (end-fixing tree, non-unimodular, semigroups) and show which step of a method fails on each |

**Calibration is the cheap early referee.** For every proposed method, a calibrator first asks which step fails
on the calibration worlds: the end-fixing tree automaton, non-unimodular groups, monoids. A method that never uses
what separates groups from those worlds is dead on arrival, and saying so costs minutes, not a verification stage.
The graph already records such steps. For example, on the end-fixing tree the random-order transport identity
fails with ratio 2, the modular function (`injective-ca-random-order-transport-identity`).

**Novelty check before calling anything new.** `bin/cairn search "<idea in words>"` and
`bin/cairn-live approaches <node>` must come before a claim's `--sig`. An idea already in the graph goes in as
`--revive` with what is new, or not at all.

**Judge rubric for design panels.** Score each proposal 0–3 on:

1. **Falsifiable first step**: something that can fail within one agent run.
2. **Calibration survival**: it uses a property that the calibration worlds lack.
3. **Distance from HOT families**: 3 when the proposal comes from a COLD family or is a new family.
4. **Payoff**: the bounty of the hole it targets.

Novelty is scored explicitly, so a panel can prefer a strange idea with a sharp first test over a safe variant of a
known dead approach.

## 4. Choosing targets: tiers and dispatch

Use `bin/cairn frontier --goal <root> --json` and `bin/cairn impact <id>`.

1. **Tier A: last-missing holes** (the `⚑ last missing for …` marker). One proof closes a route. These are the
   cheapest real wins, so give them solver → referee.
2. **Tier B: holes with a live path and prior attempts.** Read the `## Attempts` section first, through
   `bin/cairn context <id> --budget 6000`. A worker that retries a recorded dead approach wastes its run.
3. **Tier C: flagship roots and their direct bridges.** Never assign "solve it". Assign *decomposition*: new routes
   whose prerequisites can each fail on their own, conditional results, and obstructions that kill a whole class of
   approaches.

**Dispatch computes the assignments.** `bin/cairn-live dispatch <goal> --slots 8 --explore 0.3` scores
(role × open hole in the goal's cone × family) triples:

- **Base score:** `log2(1 + bounty)` × role weight × temperature novelty, where temperature novelty is COLD 3,
  warm 1.5, HOT 0.6.
  - A hole's bounty is the number of claims that `cairn`'s solver newly establishes if the hole is forced true. It
    is cached per established set in `live/bounty-cache.json`.
- **Boosts:**
  - the obstruction-miner, for dead attempts in its family;
  - any slot, for live needs and transfer targets on its hole.
- **Portfolio:** chosen greedily with diminishing returns: ×0.5 for the same node, ×0.7 for the same role, ×0.6 for
  the same family.
- **Explore quota:** 30% of slots are reserved for COLD or barely touched families.

Each slot comes with its card command and a lease signature.

`--take` atomically claims the top slot for `$CAIRN_AGENT` and prints it as JSON, with `--role` to restrict it. So
**workers self-dispatch**. The orchestrator launches N identical workers and each one pulls its own assignment from
the live state. Later workers see earlier leases, and the portfolio spreads itself. The first dispatch on a goal
takes ~22 s, and later ones reuse the bounty cache.

Take at most ~10 targets per wave. Tier A goes wide, while Tier C gets 1–2 deep lanes plus explore slots.

## 5. Lane shapes

Each lane is one Workflow run. It should stay under ~10 agents unless the user raises the size.

- **Tier A lane: solve → verify → land.**
  1. One solver writes nodes, a route and artifacts in its own worktree.
  2. A calibrator pass, which is cheap.
  3. Two adversarial referees, with different lenses (proof gaps; citation and hypothesis match), each try to
     refute it.
  4. It lands only if neither refutes it.
- **Tier C lane: understand → design → attack → verify.**
  1. One reader builds a map of the claim's cone: `atlas`, `approaches`, dead attempts, known cases.
  2. A judge panel of 3, **each in a different role**, proposes decompositions. Score them with the rubric in
     Section 3.
  3. Parallel attackers take the winning decomposition's prerequisites, each posting needs and lemmas as they go.
  4. Adversarial verify on anything claimed ESTABLISHED.
  5. A completeness critic asks what is missing: a known case never checked, a hypothesis never used, a COLD family
     never tried.
- **Pull wave:** N identical self-dispatching workers (Section 10). Best when the cone has many holes and no single
  decomposition is obviously right.

## 6. Worker contract (paste into every worker prompt)

1. **Identity.** `export CAIRN_AGENT=<label> CAIRN_WAVE=<wave>`.
2. **Before starting,** either:
   - run `bin/cairn-live dispatch <goal> --take --json` and read the printed `card` command's output; or
   - for an assigned hole, run `bin/cairn search "<idea>"` and `bin/cairn-live approaches <id>`, then
     `bin/cairn-live claim <id> --family <f> --sig "<idea in 3–8 words>" --intent "<first falsifiable step>"`.

   Exit 3 means blocked. Pick a different idea (not a synonym) or a different hole.
3. **While working:**
   - `bin/cairn-live feed --new --cone <goal>` at every checkpoint. Someone may just have proved your lemma or killed
     your approach.
   - `heartbeat --node <id> --text "<progress>"` at least hourly.
   - Post `lemma` as soon as a sub-result is established, and `need` the moment you are blocked on a statement.
   - Post `spark` for side ideas you will not pursue.
4. **Files.** Write only **new** files under `research/` and `experiments/<topic>-<date>/`. Edit only the frontmatter
   and `## Attempts` of the one claim you target. Never touch `research/FRONTIER.md` (it is generated), or the
   `notes/` files of other lanes.
5. **Lint.** Ids must match `^[a-z0-9][a-z0-9-]{1,63}$`. Every claim needs `distinct_from` for its near duplicates,
   and every artifact path must exist.
6. **Status honesty.**
   - A claim is ESTABLISHED only through a complete route whose prerequisites are established or imported with a
     verbatim citation.
   - Anything else stays OPEN, with the work recorded under `## Attempts`.
   - Computations go in `experiments/` as a runnable script, and the claim names it in `artifacts`.
7. **Ending.**
   - A failed approach ends with `bin/cairn-live dead <id> --text "<the step where it dies>"`. A recorded dead end
     is a result.
   - Anything else ends with `release`.
8. **Handoff.** `bin/cairn check` must exit 0 on your worktree. Return the list of files you added, the target id,
   the claimed status and a one-paragraph proof sketch. Never commit to main yourself.

## 7. Landing: `tools/cairn-land.sh`

One verified result, one commit, landed without touching anyone's working tree:

```sh
CAIRN_LAND_TRAILERS=/path/to/trailers.txt \
tools/cairn-land.sh -m "Establish <id> via <route>" [-F body.md] --mirror <session-branch> --node <id> \
  <worker-worktree> research/<id>.md research/<id>-proof.md experiments/<topic>-<date>
```

The lander:

1. takes `live/land.lock` (container-wide `flock`);
2. builds a temporary worktree at `origin/main` and copies the paths in;
3. runs `bin/cairn check` (exit 0 required, else exit 4 and nothing is pushed);
4. stages the paths plus the regenerated `research/FRONTIER.md`, commits and pushes;
5. **on a rejected push, never rebases or forces.** It rebuilds on the new `origin/main`, copies again, re-checks
   and recommits, so the generated frontier never conflicts. It gives up after 6 attempts;
6. mirrors to `--mirror BRANCH` only as a fast-forward;
7. posts a `landed` event to the bus.

Exit codes: 0 landed or nothing to land, 4 missing path or failed check, 64 usage, 1 gave up.

Land as each result verifies. Never batch to the end of the run: an outage then loses verification but not the work.
Refuted or unverified work still lands, as OPEN attempts.

## 8. Reporting to the user

Report by verification tier, never as one total:

- **Established, refereed**: a route is complete and two referees failed to refute it.
- **Established, agent-verified only**: one referee, or referee stages lost.
- **Refutations**, and the routes they invalidated.
- **Open, with new routes or obstructions**: decompositions, conditional results, dead classes.
- **Paradigm coverage**: which families were tried, and which COLD families produced anything. From `atlas` and
  `board`.
- **Not landed**, and why.

Check `git log origin/main --oneline` before saying anything about landing.

## 9. Outages and salvage

- Workflows journal their agent results. Resume with `resumeFromRunId` unless the user has said not to resume.
- The bus survives outages: leases of dead workers expire by TTL, and `board` shows what each had reached.
- **Salvage pass** after any abnormal end:
  1. `git status --short` in each worktree;
  2. `bin/cairn check`;
  3. triage each uncommitted target (checker-clean and referee-passed; checker-clean only; broken);
  4. land the first two groups with `tools/cairn-land.sh` and honest status;
  5. quarantine the third under `wip/` with a note.

## 10. Workflow skeletons

**Pull wave** (self-dispatch; the orchestrator does not choose targets):

```js
export const meta = {
  name: 'cairn-pull-wave',
  description: 'Self-dispatching workers take role x hole x family slots from the live bus and referee results',
  phases: [{ title: 'Work' }, { title: 'Referee' }],
}
const RESULT = { type: 'object', properties: {
  id: { type: 'string' }, role: { type: 'string' }, family: { type: 'string' },
  status: { enum: ['ESTABLISHED', 'OPEN', 'REFUTED', 'DEAD'] },
  worktree: { type: 'string' }, files: { type: 'array', items: { type: 'string' } },
  sketch: { type: 'string' } }, required: ['id', 'status', 'files', 'sketch'] }
const VERDICT = { type: 'object', properties: { refuted: { type: 'boolean' }, reason: { type: 'string' } },
  required: ['refuted', 'reason'] }
const LENSES = ['gaps in the proof steps', 'hypotheses and citations: does each import say exactly what is used',
                'calibration: which step fails on the end-fixing tree automaton, and does the proof use why']

return await pipeline(Array.from({ length: args.workers }, (_, i) => i),
  i => agent(`${args.contract}\n\nexport CAIRN_AGENT=w${i} CAIRN_WAVE=${args.wave}\n` +
             `Self-dispatch: bin/cairn-live dispatch ${args.goal} --take --json, then run the printed card command.`,
             { label: `work:w${i}`, phase: 'Work', isolation: 'worktree', schema: RESULT }),
  r => r.status !== 'ESTABLISHED' ? { ...r, votes: [] } :
    parallel(LENSES.map(lens => () => agent(
      `Try to refute this result through the lens "${lens}". Default refuted=true if unsure. ` +
      `Post the outcome: bin/cairn-live verdict ${r.id} --outcome refuted|survives --text "<reason>".\n` +
      `Worktree: ${r.worktree}\nFiles: ${r.files.join(', ')}\nSketch: ${r.sketch}`,
      { label: `referee:${r.id}`, phase: 'Referee', schema: VERDICT })))
      .then(votes => ({ ...r, votes, survives: votes.filter(Boolean).every(v => !v.refuted) })))
// The orchestrator lands each result with tools/cairn-land.sh: survivors as ESTABLISHED, the rest as OPEN attempts.
```

Pass `args = { workers: 8, wave: '<name>', goal: '<goal id>', contract: <Section 6 text> }`. Starting workers at
the same moment is safe, because `--take` is atomic and the diversity rule applies per claim.

**Tier A wave** (targets chosen by the orchestrator): the same pipeline, with the first stage prompted `Target
hole: <id>` and the claim step of Section 6 in place of `--take`.

## 11. Paradigm lanes for the Gottschalk cone

Each lane is one idea that is not in the graph, checked with `bin/cairn search` on 2026-09-17. Each comes with its
nearest nodes and a first step that can fail within one run. All are OPEN proposals, not results.

**(a) Quantum surjunctivity (transplanter; operator-algebras is COLD).**

- **Conjecture:** over every group `G`, every `G`-equivariant, finite-propagation, unital *-endomorphism `Φ` of the
  quasi-local algebra `⊗_G M_d` is surjective.
- **What comes for free:**
  - `Φ` is injective automatically, because the algebra is simple, so "strict" means "not onto".
  - The unique trace is preserved, so `Φ` extends to the hyperfinite II₁ factor and has a **Jones index**
    `[R : Φ(R)]`. Strictness means index > 1, and the index can only take Jones' values.
- **Paradigm shift:** the classical question lives on the diagonal. A strict classical automaton `τ` has a left
  inverse `σ` that is surjective and not injective, and the pullback of `σ` is an injective, non-surjective
  endomorphism of the diagonal. Whether it extends to a trace-preserving quantum one is exactly a single-site balance
  statement, `every-injective-ca-has-uniform-single-site-output-law`. So the quantum conjecture is a *stronger*
  statement with more rigid invariants (index quantization, Connes–Størmer entropy), which might be easier to prove.
- **Nearest nodes:** `every-injective-ca-preserves-uniform-bernoulli-measure`,
  `trace-preserving-endomorphism-fixes-discrete-type-i-summand`, the Jones-index nodes, and
  `injective-ca-images-have-full-single-site-entropy`.
- **First steps:**
  1. Wiring endomorphisms `(g, i) ↦ g s_i` never compress, on any group. This is easy and gives a node.
  2. Amenable `G`: Connes–Størmer entropy additivity gives surjectivity.
  3. Nonamenable test: a computer search on `F_2`, `d = 2`, propagation `{1, a, b}`, over the finite variety of
     matrix-unit assignments whose translates commute. Any strict solution is new and is a counterexample candidate.

**(b) Track deficit as an information-transport index (obstruction-miner).**

- **The shared step:**
  - Section 5, items 5–8, of `notes/gottschalk-surjunctivity-conjecture-frontier-swarm-2026-09-16.md` all die
    "one `A`-track short" at the star annulus.
  - Item 7 adds that reversible conjugation never supplies the track.
  - Item 8 dies because Garden-of-Eden slack cannot be moved to where the track is needed.
- **Proposal:** make "track" a number. Apply the random-order transport identity (`log |A|` out of every output
  site, `injective-ca-random-order-transport-identity`) to a design on `(A ⊔ {*})^G`. The deficit is transport in
  minus transport needed at a boundary star site.
- **Conjecture shape:**
  1. The deficit is invariant under composition with reversible automata.
  2. It equals `log |A|` for every design in the class "`τ` and `σ` off the star set, raw or default on it".
- **What the invariant buys:** it would kill the class in one theorem. It would also name the gate: a design must
  move Garden-of-Eden slack by a *configuration-dependent* paradoxical transport. Equivariant local rules can move
  mass only by translations, which are bijective, so the markers must come from `τ`'s own missing patterns.
- **Nearest nodes:** `injective-ca-random-order-transport-is-dominated` (bounty 13–14),
  `rokhlin-window-transport-is-dominated` (bounty 29–30), `single-fibre-garden-of-eden-transplant-proof`.
- **First step:** compute the deficit for designs 6 and 7 on a small `F_2` window. If it is not `log |A|`, the
  bookkeeping is wrong and the class is not uniform, which is itself informative.

**(c) Index = modular imbalance (calibrator, then reframer).**

- **The observation:** the end-fixing tree calibration pays for strictness by a transport imbalance of ratio 2, the
  modular function. Domination still holds there (the `## Attempts` of
  `injective-ca-random-order-transport-is-dominated`).
- **Proposal:** find the invariant that the ratio 2 *is*.
  - **Candidate:** the Jones index, or the Radon–Nikodym cocycle, of the endomorphism that the tree automaton
    induces on the von Neumann algebra of its orbit groupoid.
  - **Conjecture shape:** strictness forces a non-trivial modular cocycle on some associated measured groupoid;
    groups (unimodular) force it trivial.
- **What it links:** this lane ties (a) and (b) together. If it holds, the flagship problem becomes "the strict
  automaton's groupoid is unimodular". That is a type of statement the graph has never attacked.
- **First step:** compute the induced endomorphism for the tree automaton and check whether its index is 2 (or
  1/2). If it is not, the correspondence is wrong and the lane dies cheaply.

**(d) Configuration-dependent paradoxical transport (inverter, then constructor).**

- **Proposal:** take the biography from (b) literally.
  - A counterexample over nonamenable `G` must hold clopen markers derived from `τ`'s Garden-of-Eden patterns.
  - It needs a local rule that uses them to route a 2-to-1 compression of star sites along the markers.
- **What exists:** Borel paradoxical decompositions exist for free actions, while continuous ones fail on the
  constant configurations. So the construction has to live on the complement of the periodic points and be patched
  there by `τ` itself.
- **Nearest nodes:** `strict-product-automata-have-no-single-fibre-garden-of-eden`,
  `sofic-radical-localizes-garden-of-eden-windows`, `measure-free-minimal-cantor-action-with-finite-clopen-type`.
- **First step:** on `F_2`, build clopen markers from a fixed Garden-of-Eden pattern of a concrete non-surjective
  map. Then check whether some finite-radius rule on the marker set realizes a 2-to-1 compression without collisions
  at overlaps (item 8's failure). This is a finite SAT instance per radius.

**(e) Hopfian subshift invariant (reframer).**

- **Proposal:** a strict automaton makes its image `τ(A^G)` a subshift conjugate to the full shift and properly
  contained in it. Call a class of subshifts *co-Hopfian* if no member embeds into itself properly by an automaton.
  The goal is then "full shifts over `G` are co-Hopfian".
- **The route to try:** find a *monotone* conjugacy invariant of subshifts (strictly decreasing under proper
  inclusion among subshifts conjugate to the full shift) that is not entropy. Entropy fails on nonamenable groups.
  - **Candidates:** the type-semigroup class of the clopen partition, or the `K_0` class of the characteristic
    projection in the crossed product.
- **First step:** calibrate on the end-fixing tree. A correct invariant must *fail* to be monotone there, and the
  step where it fails names what it uses about groups.

**Scale-shifter note.** The tester-host reduction (`positive-rokhlin-entropy-on-one-host-proves-gottschalk`) already
changes the quantifier level. Any lane above that works on one host is enough.

## 12. Testing the tooling

```sh
python3 -m unittest tools/test_cairn_live.py
```

The tests cover:

- the same idea is blocked, and the same family needs a reason;
- a dead idea needs `--revive`, and release frees the approach;
- expiry and heartbeat;
- `feed --new` skips the agent's own events and advances its cursor;
- adopting a spark closes it;
- merge is a union by id and tolerates a torn line;
- usage errors exit 64, including a missing agent;
- 16 concurrent forked claims admit exactly one.

`tools/cairn-land.sh` was exercised against a bare test remote, including the rejected-push rebuild path. Never patch
the vendored `tools/cairn.py`. The bus uses it only as a library (`compile_graph`, `goal_cone`, `similar_nodes`).
