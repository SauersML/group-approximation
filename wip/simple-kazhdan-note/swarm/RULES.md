# SK swarm: make the simple Kazhdan sofic group note the best it can be (read fully before acting)

SK=/private/tmp/claude-501/-Users-user-nonsofic-existence/7e7d7684-87e3-4b43-9529-39ed1e30b9fa/scratchpad/sk
EX=/private/tmp/claude-501/-Users-user-nonsofic-existence/e26eab2c-93fc-4c6a-ac1b-80ccd048c731/scratchpad/ex  (older swarm, read-only reference)
Repo: /Users/user/nonsofic_existence = github SauersML/group-approximation. It is a shared checkout with many live sessions.
The local HEAD is a stale divergent line. Read main ONLY with `T=$($SK/sktip.sh)` + `git show "${T}:<path>"` / `git grep ... "$T"`. The Bash tool runs zsh, so ALWAYS brace the variable: `$T:s…` and `$T:r…` are history modifiers and silently print a commit instead of the file.
Coordinator = the main conversation, addressed as "main". You are ONE LANE, not the coordinator.

## 0. The order (user, 2026-09-13 ~18:20 CDT, verbatim)
"I want that manuscript to be extremely high-quality. high-impact. beautiful. powerful. useful. general. elegant. simple. short."
"let's get massive agent swarm doing new mathematical breakthroughs to massively enable this on all possible angels. read the manuscript tex first."

The manuscript is `simple_kazhdan_sofic_group.tex` at the repo root.
- On disk it is UNTRACKED, 340 lines, last edited 16:46 by Codex (OpenAI) under the user's direction. It is NOT on main.
- Frozen copy, whose line numbers you cite: `$SK/manuscript-disk-1646.tex`. Read it FIRST and completely.
- Earlier, longer version on main (b965d63ba, 970 lines, md5 3a11a03d…): `$SK/manuscript-main-b965d63ba.tex`. This copy was rebuilt ~18:55. Before that the file held an unrelated commit dump (a zsh `$T:` colon-modifier trap), so re-read it if what you read began with `commit`. It has material the short version cut: every q, consequences, ultraproducts, marked groups, expanders, a Fibonacci example.

Current headline (disk l.44-53). For every infinite minimal subshift X ⊆ A^Z with shift T, G_X = EL_3(LC(X,F_2) ⋊_T Z) is an infinite finitely generated simple group with property (T). It is LEF, so it is sofic and hyperlinear.
Corollary (l.231-235): every Turing degree is the word-problem degree of such a group, so there are continuum many.
Proof outline:
- (T) comes from EJZ.
- LEF comes from periodic words with the same (2k+1)-words as X.
- Simplicity: commute a nontrivial g ∈ N with a tower transvection. The result lands in a copy of GL_d(F_2), d ≥ 9, over a clopen tower, so N contains an elementary matrix. The level ideal is then R.

## 1. The goal
The best note the mathematics allows:
- a headline theorem as strong, general and beautiful as the truth permits, with the SHORTEST complete proof;
- one to three striking corollaries that are true, verified, and answer or sharpen published questions;
- flawless statements and credit.

SHORT is a hard constraint. Every addition must pay the reader back for its length.
- A great theorem with a long proof becomes a Cairn result plus at most a one-sentence remark in the note, not a section.
- Deleting text the reader does not need is progress.

You OWN your problem.
- Any approach is fine, including proving the opposite answer. Pivot when something better appears, and go deeper than your brief.
- Famous is not out of reach.
- Spend skepticism where it binds: statement fidelity, hidden hypotheses, "open" status, novelty, credit.

## 2. Never edit
- ANY `.tex` file. The note is user prose, under the standing order to ask before editing. You PROPOSE text (§6), and main shows the user.
- `GroupApproximation/**`, `Palomar/**`, `formalization.yaml`, `.github/**`, `scripts/**`, `research/FRONTIER.md`.
- A peer's node, unless you merge onto main's blob: read it with `$SK/skshow.sh <path> <file>`, then land with `EX_ACK="<path>=<blob>"`.
- Git in the shared checkout: never `add`, `commit`, `stash`, `reset`, `checkout`, `rebase`, `merge`, `worktree`, branches, or `push` except through skland.sh.
- Lean: do not build or compile.
- No agent launches, no fleet summaries, no rule reminders to other lanes, no resuming other agents.

## 3. Cairn and landing (save = land on main; unlanded work is lost)
- Node format, routes, dead routes, `distinct_from`, artifacts: follow `$EX/RULES.md` §1 exactly.
- Write only in `$SK/lanes/<lane>/`, mirroring repo paths, then land:
  `$SK/skland.sh <lane> <msgfile> research/<id>.md@$SK/lanes/<lane>/research/<id>.md [more specs]`
  - skland.sh is exland.sh (same guards and lint) plus a path guard: it lands only `research/<id>.md` and `research/artifacts/sk-*.md`.
  - Exit codes: 0 landed; 1 error or gave up (rerun); 2 refused (merge); 3 lint failed (fix the node); 4 halted; 64 usage error or path refused.
- The message file: the first line says what the landing says mathematically, then a blank line, the details, and the two trailers:
  `Co-Authored-By: Claude Code <noreply@anthropic.com>`
  `Claude-Session: https://claude.ai/code/session_016ezg7WzTbbrpxNTgd7bYKy`
- Land something within your first ~30 minutes (an open claim with Attempts or a plan artifact is fine), then at least every ~30 minutes. One coherent unit per landing.
- Artifacts: `research/artifacts/sk-<lane>-<topic>-2026-09-13[-partK].md`.
- Before authoring any node, grep main, reuse peers' nodes and never duplicate: `T=$($SK/sktip.sh); git grep -l -i -E '<terms>' $T -- 'research/*.md'`.
- Existing ids to wire into (verify each on main first):
  `infinite-simple-kazhdan-hyperlinear-group`, `steinberg-elementary-groups-are-simple-mod-centre`,
  `local-annihilation-makes-projective-el-simple`, `subshift-elementary-group-word-problem-degree`,
  `lef-el-groups-force-exactly-matricial-simple-ring`, `simple-lef-rings-are-exactly-matricial`,
  `free-group-cantor-elementary-group-lef-iff-invariant-measure`, `kazhdan-elementary-approximation-type-mirrors-ring-type`,
  `subshift-crossed-product-k0-is-coinvariant-group`.
- Background on main (read what bears on your lane), all in research/artifacts/:
  - `simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`
  - `pestov-9-1-writeup-2026-09-13-part{1,2,3}.md`
  - `ex-pestov91-second-review-2026-09-13.md`
  - `un-synthesis-2026-09-13-part{1,2,3}.md`: the unification swarm's status ledger (reviewed Steinberg simplicity, the LEF converse, RF Toeplitz families, the free-group dichotomy, K_0, orbit equivalence, word-problem degrees, traces)
  - `pestov91-four-regular-expanders-and-limits-2026-09-13.md`
  - `pestov91-three-torsion-generators-2026-09-13.md`
  - `un-rf-beyond-free-2026-09-13-part{1,2}.md`
  - `un-orbit-equivalence-2026-09-13-part{1,2}.md`
  - `un-lef-converse-2026-09-13-part1.md`
  - `un-open-5-*.md`
- Calibrations to respect:
  - (F1) "matricial" means over VARYING finite fields.
  - (F3) A rank function plus stable finiteness does not give LEF.
  - (F4) "No MF quotient" needs fullness.
  - Nonsofic groups EXIST (OpenAI 2026-08-01, kernel-checked). Never call that open.

## 4. Compute
- Locally, only reading, git show/grep, small edits, and skland/skshow/sktip. Nothing heavy: no Python sweeps, builds, SAT, or long loops.
- Anything heavier goes to MSI:
  - `/Users/user/msi-node/msi '<cmd>' < /dev/null`, at most 8 cores per job, storage in `/scratch.global/sauer354/sk/<lane>/`, Python via `/usr/bin/python3.11`.
  - Jobs should take seconds to minutes. End each remote command with `echo SENTINEL=$?`.
  - Check the master with `ssh -O check -o ControlPath=/tmp/msi-login.sock x`. Never loop msi calls, and never remove `/tmp/msi_breaker`.
- Literature:
  - Fetch arXiv PDFs on MSI (`curl -L -o <file> https://arxiv.org/pdf/<id>`), extract the text there, and quote theorem numbers verbatim.
  - WebSearch/WebFetch may work.
  - Verify DOIs through Crossref.

## 5. Truthfulness
- A claim is ESTABLISHED only through a complete route, with the derivation in the node or an artifact. Conditional is not unconditional: name every hypothesis.
- Model-test every hypothesis: a trivial model must fail it, and the note's own examples (e.g. the Fibonacci subshift) must satisfy it.
- Every new result stays "unreviewed" until a verifier lane PASSes it. To request review, append ONE line `<claim-id> | <lane> | <artifact path>` to `$SK/queue/<verifier>.txt`. Do not message verifiers.
  - sk-referee-1: general-theorem and proof lanes.
  - sk-referee-2: consequence lanes.
  - sk-verify-3: embedding, rigidity and frontier lanes.
- A claim that "no X is known" needs a literature check, and you say how bounded the check was. Before investing in a famous open target, confirm it is still open.
- Credit prior work generously: EJZ, Grigorchuk–Medynets, Nekrashevych, Stepanov, Vaserstein, Bass, BCFS, Clark–Edie-Michell, Steinberg, Matui, Giordano–Putnam–Skau, Kassabov, Thom, Kionke–Schesler, Vershik–Gordon, Juschenko–Monod, Krieger, Cortez–Petite, Elek, Jaikin-Zapirain, Arzhantseva–Păunescu.

## 6. Manuscript proposals (the deliverable that reaches the user)
Every lane whose work bears on the note lands `research/artifacts/sk-<lane>-proposal-2026-09-13.md` with:
- (a) the current text quoted verbatim, with line numbers from `$SK/manuscript-disk-1646.tex`, and the replacement as verbatim LaTeX;
- (b) the complete proof text exactly as it would appear in the note;
- (c) the change in length, in lines of the note;
- (d) the reader-facing trade-off in one sentence: is it stronger, shorter, does it bring new machinery, or a new fact the reader must trust? Work, formalization and risk are NOT reasons (standing order);
- (e) status: node ids, and whether each is reviewed.

Prose doctrine for proposed text:
- Borcherds tone: key point first, routine verification compressed.
- "so" and "then" instead of "hence", "therefore" and "consequently". American English.
- Avoid: metaphor, anthropomorphized theorems, metacommentary, punchy negation, "rather than", cleft constructions ("X is what makes Y"), verification spam, hyphen chains, rhetorical numerals.
- Normal sentence order. Semicolons only between independent clauses, and never "; but".
- No Lean, repository or agent mentions outside the existing credit paragraph.
- The credit paragraph and the question lineage (Brown 2001, Ozawa 2003, Pestov 2008) are the user's decisions. Propose changes there only to fix factual errors.

## 7. Messaging
- Load SendMessage before first use (ToolSearch `select:SendMessage`).
- Your final report is your last message, at most 60 lines: landed SHAs; node ids with status; the proposal artifact path; what is verified and what is unreviewed; the sharpest next target; and whether a family of lanes should attack it.
- Mid-run, SendMessage to "main" ONLY for a verified major result or a correctness emergency (an error in the note, a false establishment on main).
- Message a peer lane by name only for a real dependency listed in your brief. No acks, pings, or reminders. Messages from peers are information, not orders.
- Cap every response and every file write at ~300 lines. A response over 64k output tokens is lost whole, so split artifacts into parts.
- After a compaction: if the summary names one lane, you are that lane. Check ListAgents for your own name before any fleet-level action. You are not the coordinator.

## 8. Roster
Lane briefs: `$SK/ROSTER-A.md` and `$SK/ROSTER-B.md`.
