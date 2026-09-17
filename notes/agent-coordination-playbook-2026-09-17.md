# Coordinating agents on big solves: playbook (2026-09-17)

Written after the September swarms: a 240-agent wave and a solo follow-up. It is for the orchestrator, the session
that launches and lands the work. Workers only need the worker contract in Section 4.

## 0. What the last swarm taught

| What happened | Cost | Rule it became |
|---|---|---|
| Shallow clone, and HEAD 61 commits behind a separate landing worktree | Checker errors that looked real | Section 1 pre-flight |
| Verifier stages died in a model outage after their solvers finished | 1,077 files and ~170 established claims sat uncommitted until a salvage pass | Land continuously (Section 5), and keep a salvage step (Section 7) |
| 30 "high-impact" workflows went straight at flagship conjectures | One partial artifact, not landed | Decompose before solving (Section 2) |
| 60 targets × (solver + referee) | 4 Zaremsky resolutions and many attempts, all checked by agents only | Fewer, deeper lanes; say what verified each result (Section 6) |
| Node ids over 64 characters, stale artifact paths | `cairn check` exit 4 at landing | The worker contract lints before handing off (Section 4) |
| "Never landed" reported for work that was actually on main | A wrong report to the user | Check `git log origin/main` before saying anything about landing |

## 1. Pre-flight (orchestrator, solo, before any agent)

```sh
git rev-parse --is-shallow-repository   # must be false, else: git fetch --unshallow
git fetch origin main && git status -sb  # clean tree, HEAD == origin/main
bin/cairn check; echo $?                 # must be 0 (warnings are fine)
bin/cairn status                         # goals, frontier size, active locks
```

Fix any exit-4 error before launching. Otherwise every worker inherits it and hands back a red graph.

## 2. Choosing targets: tiers, not a flat list

Use `bin/cairn frontier --goal <root> --json` and `bin/cairn impact <id>`.

1. **Tier A: last-missing holes** (the `⚑ last missing for …` marker). One proof closes a route. These are the
   cheapest real wins, so give them solver → referee.
2. **Tier B: holes with a live path and prior attempts.** Read the `## Attempts` section first, through
   `bin/cairn context <id> --budget 6000`. A worker that retries a recorded dead approach wastes its run.
3. **Tier C: flagship roots and their direct bridges** (for example `nonsurjunctive-alphabet-sizes-are-upward-closed`).
   Never assign "solve it". Assign *decomposition*: new routes whose prerequisites can each fail on their own,
   conditional results, and obstructions that kill a whole class of approaches. The count-preservation claim of
   2026-09-17 is the model for this.

Take at most ~10 targets per wave. Tier A goes wide, while Tier C gets 1–2 deep lanes.

## 3. Lane shapes

Each lane is one Workflow run. It should stay under ~10 agents unless the user raises the size.

- **Tier A lane: solve → verify → land.**
  1. One solver writes nodes, a route and artifacts in its own worktree.
  2. Two adversarial referees, with different lenses (proof gaps; citation and hypothesis match), each try to
     refute it.
  3. It lands only if neither refutes it.
- **Tier C lane: understand → design → attack → verify.**
  1. One reader builds a map of the claim's cone: routes, dead attempts, known cases.
  2. A judge panel of 3 proposes independent decompositions and scores them.
  3. Parallel attackers take the winning decomposition's prerequisites.
  4. Adversarial verify on anything claimed ESTABLISHED.
  5. A completeness critic asks what is missing: a known case never checked, or a hypothesis never used.

## 4. Worker contract (paste into every worker prompt)

1. Before starting a hole, run `CAIRN_AGENT=<label> bin/cairn lock <id> --ttl 4h`. Exit 3 means someone else holds
   it: pick the next hole or stop. Unlock when done.
2. Write only **new** files under `research/` and `experiments/<topic>-<date>/`. Edit only the frontmatter and
   `## Attempts` of the one claim you target. Never touch `research/FRONTIER.md` (it is generated), or the `notes/`
   files of other lanes.
3. Ids must match `^[a-z0-9][a-z0-9-]{1,63}$`. Every claim needs `distinct_from` for its near duplicates, and every
   artifact path must exist.
4. Status honesty:
   - A claim is ESTABLISHED only through a complete route whose prerequisites are established or imported with a
     verbatim citation.
   - Anything else stays OPEN, with the work recorded under `## Attempts`.
   - Computations go in `experiments/` as a runnable script, and the claim names it in `artifacts`.
5. Before handing off, `bin/cairn check` must exit 0 on your worktree. Return the list of files you added, the target
   id, the claimed status and a one-paragraph proof sketch.
6. Never commit to main yourself. The lander does that (Section 5).

## 5. Landing: one serialized lander, commit per target

- The orchestrator, or a single lander agent, owns `main`. Workers return patches or worktree paths.
- For each verified result:
  1. copy its files in;
  2. run `bin/cairn check` (exit 0);
  3. commit with the trailers;
  4. `git push origin HEAD:main`, then mirror to the session branch.
- Land as each result verifies. Never batch to the end of the run: an outage then loses verification but not the
  work.
- On push rejection, run `git fetch origin main`, rebase (these are new files, so conflicts are rare), re-check and
  push. Never force-push main.
- Refuted or unverified work still lands, as OPEN attempts. A recorded dead end is useful graph content.

## 6. Reporting to the user

Report by verification tier, never as one total:

- **Established, refereed**: a route is complete and two referees failed to refute it.
- **Established, agent-verified only**: one referee, or referee stages lost.
- **Refutations**, and the routes they invalidated.
- **Open, with new routes or obstructions**: decompositions, conditional results, dead classes.
- **Not landed**, and why.

Check `git log origin/main --oneline` before saying anything about landing.

## 7. Outages and salvage

- Workflows journal their agent results. Resume with `resumeFromRunId` unless the user has said not to resume.
- **Salvage pass** after any abnormal end:
  1. `git status --short`;
  2. `bin/cairn check`;
  3. triage each uncommitted target (checker-clean and referee-passed; checker-clean only; broken);
  4. land the first two groups with honest status;
  5. quarantine the third under `wip/` with a note.

## 8. Workflow skeleton (Tier A wave)

```js
export const meta = {
  name: 'cairn-tier-a-wave',
  description: 'Solve, adversarially referee, and return landable patches for last-missing Cairn holes',
  phases: [{ title: 'Solve' }, { title: 'Referee' }],
}
const RESULT = { type: 'object', properties: {
  id: { type: 'string' }, status: { enum: ['ESTABLISHED', 'OPEN', 'REFUTED'] },
  worktree: { type: 'string' }, files: { type: 'array', items: { type: 'string' } },
  sketch: { type: 'string' } }, required: ['id', 'status', 'files', 'sketch'] }
const VERDICT = { type: 'object', properties: { refuted: { type: 'boolean' }, reason: { type: 'string' } },
  required: ['refuted', 'reason'] }
const LENSES = ['gaps in the proof steps', 'hypotheses and citations: does each import say exactly what is used']

return await pipeline(args.targets,
  t => agent(`${args.contract}\n\nTarget hole: ${t}. Follow the worker contract.`,
             { label: `solve:${t}`, phase: 'Solve', isolation: 'worktree', schema: RESULT }),
  r => r.status !== 'ESTABLISHED' ? { ...r, votes: [] } :
    parallel(LENSES.map(lens => () => agent(
      `Try to refute this result through the lens "${lens}". Default refuted=true if unsure.\n` +
      `Worktree: ${r.worktree}\nFiles: ${r.files.join(', ')}\nSketch: ${r.sketch}`,
      { label: `referee:${r.id}`, phase: 'Referee', schema: VERDICT })))
      .then(votes => ({ ...r, votes, survives: votes.filter(Boolean).every(v => !v.refuted) })))
// The orchestrator lands each survivor (Section 5) and downgrades the rest to OPEN attempts.
```

Pass `args = { targets: [...ids], contract: <Section 4 text> }`.

## 9. Candidate first wave (Gottschalk cone, from `bin/cairn frontier --goal gottschalk-surjunctivity-conjecture`)

- **Tier A (last missing):**
  - `nonsurjunctive-alphabet-sizes-are-upward-closed`
  - `surjunctivity-failure-descends-to-binary-alphabet`
  - `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`
  - `fg-simple-kazhdan-groups-are-surjunctive`

  All four are hard, so treat them as Tier C lanes despite the marker.
- **Tier B (smaller, testable):**
  - `binary-four-plus-memory-automata-are-surjunctive`
  - `f2-support-three-one-sided-units-are-units`
- **Tier C decomposition:** `some-nonsurjunctive-group-gives-a-binary-power-one`, with notes item 6.3 (spare-track
  annulus) as the design question.
