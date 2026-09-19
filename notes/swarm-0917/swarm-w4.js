export const meta = {
  name: 'swarm-0917-lanes',
  description: 'High-impact cairn lanes: worker in a worktree, three-lens referee on established claims, conflict-free landing on main',
  phases: [{ title: 'Work' }, { title: 'Referee' }, { title: 'Land' }],
}

// args = { prefix, wave, busRef, trailers, referee?: false, lanes: [{ key, goal, mode: 'pull'|'target'|'lane', node?, role?, text? }] }
// referee: false skips the referee stage: solve first, review after something is solved. Workers' statuses land as they are.
const REFEREE = args.referee !== false
const ENV = `CAIRN_AGENT=__AGENT__ CAIRN_WAVE=${args.wave} CAIRN_LIVE_SYNC=origin CAIRN_LIVE_REF=${args.busRef}`

const RESULT = { type: 'object', properties: {
  id: { type: 'string' }, role: { type: 'string' }, family: { type: 'string' },
  status: { type: 'string', enum: ['ESTABLISHED', 'OPEN', 'REFUTED', 'DEAD'] },
  worktree: { type: 'string' }, files: { type: 'array', items: { type: 'string' } },
  established: { type: 'array', items: { type: 'string' } },
  sketch: { type: 'string' }, impact: { type: 'string' } },
  required: ['id', 'status', 'worktree', 'files', 'established', 'sketch', 'impact'] }
const VERDICT = { type: 'object', properties: { refuted: { type: 'boolean' }, reason: { type: 'string' } },
  required: ['refuted', 'reason'] }
const LANDED = { type: 'object', properties: { landed: { type: 'boolean' }, commit: { type: 'string' },
  final_status: { type: 'string' }, note: { type: 'string' } }, required: ['landed', 'commit', 'final_status', 'note'] }
const LENSES = [
  'gaps in the proof steps: find the first step that does not follow',
  'hypotheses and citations: does each import say exactly what is used, with the same quantifiers and hypotheses',
  'calibration: which step fails on the end-fixing tree automaton, non-unimodular groups or monoids, and does the proof use what separates groups from them',
]

const HIGH_IMPACT = `You are one worker in a 100+ agent research swarm on the group-approximation repository (a cairn research graph of claims and routes toward major open problems in group theory, dynamics and complexity).
HIGH IMPACT ONLY. The user was explicit: no boring special cases. A result counts only if it does one of:
  (1) closes a hole that is last-missing on a route toward a flagship goal, or proves/disproves a hole with large bounty;
  (2) builds a new decomposition of a flagship statement into prerequisites that can each fail on their own;
  (3) kills a whole class of approaches with a precise obstruction (name the invariant and the step where every member dies);
  (4) finds a counterexample or a computation that changes what is believed.
Do not prove small instances that no route uses. If your assignment turns out to be a narrow special case, climb to the general statement it serves, or pivot to the nearest hole that matters and say why.
Be rigorous and honest: a claim is ESTABLISHED only with a complete route whose prerequisites are established or imported with verbatim citations; otherwise keep it OPEN and record the work under ## Attempts. A recorded dead end with the exact step where it dies is a real result.
Aim to SOLVE: go for the full statement, not a report about it. Keep each single response short: write long proofs to files in several small Write/Edit calls rather than one huge message.`

const CONTRACT = `CONTRACT. First read notes/agent-coordination-playbook-2026-09-17.md Sections 2, 3 and 6 (Section 6 is your contract; follow it exactly). Key points:
- Bash environment variables do NOT persist between Bash calls. Prefix EVERY bin/cairn-live command with: __ENV__
  This bus is shared live across several cloud sessions; leases, needs, lemmas and dead ends from other sessions show up in feed/board.
- Before starting: bin/cairn search "<idea>" and bin/cairn-live approaches <id>, then claim the approach (exit 3 = blocked: pick a genuinely different idea or hole).
- While working: feed --new --cone <goal> at every checkpoint; heartbeat --node <id> --text "<progress>" at least hourly; post lemma when a sub-result is established, need when blocked on a statement, spark for side ideas.
- Files: write only NEW files under research/ and experiments/<topic>-2026-09-17/. Edit only the frontmatter and ## Attempts of the one existing claim you target. Never touch research/FRONTIER.md. Ids match ^[a-z0-9][a-z0-9-]{1,63}$; add distinct_from for near duplicates; every artifact path must exist.
- Never commit, never push, never land. The orchestrator lands your work.
- End: bin/cairn-live dead <id> --text "<where it dies>" for a failed approach, else release <id>. bin/cairn check must exit 0 in your worktree before you return.
RETURN (structured): worktree = absolute output of pwd; files = every path you added or modified, relative to the repo root (from git status --short, excluding research/FRONTIER.md and .cairn/); id = main target id; established = ids you newly set ESTABLISHED (empty if none); status; role; family; sketch = one-paragraph proof or obstruction sketch; impact = which route or goal this advances and how.`

function assignment(l) {
  if (l.mode === 'pull') return `ASSIGNMENT (self-dispatch on goal ${l.goal}): run \`__ENV__ bin/cairn-live dispatch ${l.goal} --take --json${l.role ? ` --role ${l.role}` : ''}\` and then run the printed card command (with the env prefix). If the take is blocked or the slot is a narrow special case, dispatch again (up to 3 times); failing that, pick the highest-bounty unleased hole from \`bin/cairn frontier --goal ${l.goal}\` and claim it with a role whose families are COLD in \`bin/cairn-live atlas ${l.goal}\`.`
  if (l.mode === 'target') return `ASSIGNMENT (target hole ${l.node}, toward ${l.goal}${l.role ? `, role ${l.role}` : ''}): read \`bin/cairn context ${l.node} --budget 6000\` including ## Attempts and \`bin/cairn impact ${l.node}\`. Run \`__ENV__ bin/cairn-live card ${l.role || 'inverter'} ${l.goal} --node ${l.node}\`. Do not retry a recorded dead approach without something new. ${l.text || ''}`
  return `ASSIGNMENT (paradigm / decomposition lane toward ${l.goal}): ${l.text}`
}

function workerPrompt(l) {
  const agent = `${args.prefix}-${l.key}`
  const env = ENV.replace('__AGENT__', agent)
  return `${HIGH_IMPACT}\n\n${CONTRACT.replace(/__ENV__/g, env)}\n\n${assignment(l).replace(/__ENV__/g, env)}`
}

function refereePrompt(r, lens, l) {
  const env = ENV.replace('__AGENT__', `${args.prefix}-ref-${l.key}`)
  return `You are an adversarial referee for a research swarm on the group-approximation cairn graph. Try to REFUTE this result through the lens "${lens}". Default refuted=true if you are unsure or the argument has an unfilled step.
Worktree (read the files there, absolute paths): ${r.worktree}
Files: ${r.files.join(', ')}
Newly established ids: ${r.established.join(', ')}
Sketch: ${r.sketch}
Also run \`cd ${r.worktree} && bin/cairn check\` and \`bin/cairn context <id> --budget 4000\` for each established id. Do not edit any file.
Post the outcome: \`${env} bin/cairn-live verdict ${r.id} --outcome refuted|survives --text "<reason in one line>"\`.
Return refuted and a precise reason (the step, and why it fails or why it holds).`
}

function landPrompt(r, l) {
  const env = ENV.replace('__AGENT__', `${args.prefix}-land-${l.key}`)
  const votes = (r.votes || []).map((v, i) => v ? `  lens ${i + 1}: refuted=${v.refuted}: ${v.reason}` : `  lens ${i + 1}: lost`).join('\n')
  return `You land one research result on origin/main of the group-approximation repo without clobbering anyone else's work. Many other landers run concurrently in other sessions.
Worktree: ${r.worktree}
Target id: ${r.id}; worker status: ${r.status}; newly established: ${r.established.join(', ') || '(none)'}
Files: ${r.files.join(', ')}
Referee votes (only for established results):\n${votes || (REFEREE ? '  (none)' : '  (no referee stage in this wave)')}
Survives referees: ${r.survives === undefined ? 'n/a' : r.survives}
Sketch: ${r.sketch}

Steps (all inside the worktree; never touch the primary checkout's working tree):
1. \`cd ${r.worktree} && git status --short\`. Confirm the listed files exist; if the worker left out a file it created (new research/ or experiments/ files), include it. Never include research/FRONTIER.md or .cairn/.
2. ${REFEREE ? 'If any referee refuted, or votes were lost for an established result: set every newly established id back to OPEN in its frontmatter and add a dated entry under ## Attempts with the referee reason (keep the proof files; they are an attempt). If all referees survived, keep ESTABLISHED.' : 'No referee stage in this wave (review comes after solving): keep the worker status exactly as it is; do not demote anything.'}
3. Commit locally in the worktree only (never push this branch): \`git add <files> && git commit -qm "local: ${l.key}"\`.
4. \`git fetch -q origin main && git merge --no-edit origin/main\`. On conflict: for research/FRONTIER.md take origin's side (it is regenerated); for any other file keep BOTH sides' content (every attempt entry, every route, the stricter status when they disagree), then commit the merge.
5. \`bin/cairn check; echo $?\` must be 0. If it fails, fix only problems in the files of this result (lint, missing distinct_from, artifact paths).
6. Land: \`CAIRN_LAND_TRAILERS=${args.trailers} ${env} tools/cairn-land.sh -m "<subject: one plain sentence saying what was established, refuted or recorded for ${r.id}>" --node ${r.id} ${r.worktree} <every path of this result, relative>\`. Exit 0 means landed; 4 means a missing path or failed check (fix and retry); 1 means it gave up (retry once).
7. Verify with \`git fetch -q origin main && git log origin/main --oneline -8\` and report the landed commit sha. Do not claim landed unless you see it on origin/main.
8. Only if you saw the commit on origin/main: free the disk with \`cd /home/user/group-approximation && git worktree remove --force ${r.worktree}\` (ignore failure). If it did not land, leave the worktree in place.
Return landed, commit, final_status (the status that landed) and a one-line note. The commit subject must not name any model.`
}

// maxWorkers bounds how many lanes hold a worktree at once (disk); a lane keeps its slot from work through landing.
const MAX = args.maxWorkers || Infinity
let active = 0
const waiters = []
async function slot(fn) {
  while (active >= MAX) await new Promise(res => waiters.push(res))
  active++
  try { return await fn() } finally { active--; const w = waiters.shift(); if (w) w() }
}

async function lane(l) {
  const r = await agent(workerPrompt(l), { label: `work:${l.key}`, phase: 'Work', isolation: 'worktree', schema: RESULT })
  if (!r) return null
  let rr = { ...r, votes: [] }
  if (REFEREE && r.established.length) {
    const votes = await parallel(LENSES.map(lens => () => agent(refereePrompt(r, lens, l), { label: `referee:${l.key}`, phase: 'Referee', schema: VERDICT })))
    rr = { ...r, votes, survives: votes.length === LENSES.length && votes.every(v => v && !v.refuted) }
  }
  if (!rr.files.length) return { lane: l.key, id: rr.id, status: rr.status, landed: false, note: 'no files' }
  const x = await agent(landPrompt(rr, l), { label: `land:${l.key}`, phase: 'Land', schema: LANDED })
  return { lane: l.key, id: rr.id, worker_status: rr.status, established: rr.established, survives: rr.survives,
           votes: rr.votes, sketch: rr.sketch, impact: rr.impact, ...(x || { landed: false, note: 'land agent lost' }) }
}

return await pipeline(args.lanes, l => slot(() => lane(l)))
