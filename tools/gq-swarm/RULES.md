# GL_n(Q) swarm (gq), 2026-09-17 — lane rules

`GQ=/private/tmp/claude-501/-Users-user-nonsofic-existence/e0e77c89-2a2c-477e-b91b-65bc2f656857/scratchpad/gq`

## 0. You are a lane, not the coordinator
You are lane `<your name>`. The coordinator is `team-lead`; its SendMessage address is `main` (use `team-lead` only if `main` fails). Do not write fleet summaries, do not send rule
reminders to other lanes, do not launch agents, do not talk to the user. Do your lane's mathematics.

## 1. Target
Root `gl-n-q-embeds-in-fp-simple-group` (landed 2598812b3; read it first):
- **G.** For every n >= 2, the countable group GL_n(Q) embeds in a finitely presented simple group.
  BBMZ survey arXiv:2306.16356v3, Problem 5.3(5) and p. 7 ("it remains an open question whether GL_n(Q) embeds
  into a finitely presented simple group"). The full survey LaTeX is in your context (the user pasted it).
- **G'.** Problem 2.7 (Bridson–de la Harpe, Kourovka 14.10): an explicit and natural finitely presented group
  containing GL_n(Q). Also open per the survey. A natural construction for G usually answers G' too.
- Known: n = 1 (Q^x countable abelian ⊂ VA); every f.g. subgroup (Zaremsky 2405.09722 Thm 1.2); BH ⇒ G.
- Obstructions (root node): **O1** divisible (Q,+) ≤ GL_n(Q) ⇒ no residually finite overgroup (so no f.g. linear,
  no self-similar/tree group, none of the repo's linear-group hosts, at any intermediate stage); **O2** n >= 3:
  SL_3(Z) excludes V and VA; **O3** Q ⊄ V; **O4** (2688d4128) VA has NO distorted cyclic subgroups (Burillo–Felipe
  arXiv:2605.09763 Thm 1, Cor 5), while BS(1,2) ≤ GL_2(Q) and Heisenberg ≤ U_3(Q) are distorted, so VA and all its
  subgroups (V, T̄, Brin's A) are dead hosts for every n >= 2, and for Aff(Q), U_3(Q). Any host needs distorted
  cyclic subgroups. Live alternative: Kojima–Sheng arXiv:2603.18410v3 put Q in nV (n >= 2); distortion in nV open.
  Every method must say which non-RF mechanism supplies divisibility AND where the distortion lives.
- **Critic rules (7ba31e626):** every construction must say (i) where SL_3(Z) sits (the root needs infinitely many n),
  and (ii) which of the three operations that can create SL_n(Q) it uses: directed union, graph of groups over
  NONTRIVIAL edges, or a Thompson-type completion (SV_G, V_d(G), germ extension, nV, RSG). Extensions, products,
  wreaths and free products never create it (d94a5ceb9). **No more natural-action obstructions**: that family is
  already covered ~6 times (443aa4795, e0cfca2b7, 4a58a2b5b, d65ff92ff, 5a140f21e, 942cdfa94).
- Known non-RF devices containing Q: Belk–Hyde–Matucci Q ≤ T̄ ≤ Brin's A ≤ VA (finite germ extensions,
  arXiv:2407.03149); Kojima–Sheng Q ≤ 2V; Mikaelian's explicit Higman embedding of Q.

## 2. Read Cairn first (user order), cheaply
- Read nodes with the Read tool at `/Users/user/nonsofic_existence/research/<id>.md` (checkout = main as of
  09-17 afternoon) or `git -C /Users/user/nonsofic_existence show origin/main:research/<id>.md` for newer files.
  Search with the Grep/Glob tools over `/Users/user/nonsofic_existence/research`, or `git grep` on origin/main.
- Before inventing anything, read the nodes nearest your approach, their `## Attempts`, and any
  `research/artifacts/*` they cite. Starting points: `type-a-action-gives-boone-higman-for-subgroups`,
  `boone-higman-type-a-class-closed-under-finite-extensions`,
  `permutational-boone-higman-iff-finitary-alternating-hosts`, `boone-higman-via-shell-germ-stabilizers`,
  `shell-cantor-embeddings-are-finite-germ-extensions`, `decidable-inputs-have-fp-shell-envelopes`,
  `leavitt-subalgebra-linear-groups-satisfy-boone-higman`, `algebra-boone-higman-conjecture`,
  `every-countable-group-embeds-in-a-simple-fp2-group`, `polynomial-linear-groups-satisfy-boone-higman`,
  `rational-linear-groups-satisfy-boone-higman`, artifacts `boone-higman-frontier-2026-09-12.md`,
  `bh-survey-open-cases-status-2026-09-12.md`.

## 3. HARD machine limits (8 GiB laptop, ~70 lanes)
- **NEVER run `bin/cairn`, `bin/cairn-live`, python, lean, lake, latex, or any computation locally.** One
  `bin/cairn search` costs 524 MB; seventy of them crash the machine. `gq-integrate` alone may run `bin/cairn check`.
- **Never `git fetch`** (the lander keeps `origin/main` fresh). Never `git worktree`, `stash`, `reset`, `checkout`,
  `commit`, `push`, `add`, or any write to `/Users/user/nonsofic_existence`. Never read multi-page PDFs locally:
  use arXiv abs/HTML pages via WebFetch.
- Allowed: Read, Grep, Glob, `git show/log/grep/cat-file` (read-only), Write/Edit inside `$GQ/work/<lane>/` and
  `$GQ/board/<lane>.md`, WebSearch/WebFetch, SendMessage, and `$GQ/gqland.sh`.
- No single tool call or message over ~300 lines. Write long artifacts section by section.

## 4. Files and node format
- Draft only under `$GQ/work/<lane>/research/<id>.md` and `$GQ/work/<lane>/research/artifacts/gq-<lane>-<topic>.md`.
- Node = Cairn rg:2 Markdown. Claim frontmatter: `rg: 2`, `id:` (= file stem, `^[a-z0-9][a-z0-9-]{1,63}$`),
  `kind: claim`, `title:`, `distinct_from:` (map: near-duplicate id → why different), optional `artifacts:` list.
  Route frontmatter: `kind: route`, `title:` (one line, REQUIRED; the lander refuses without it), `target: <claim id>`, `requires:` list (every id must exist on main or in the
  same landing). Proof of an established claim = route `<claim>-proof` with `requires:` its inputs.
- Body starts with the bold status: `**OPEN.**` or `**ESTABLISHED (...)**` and the exact statement; then proof or
  `## Attempts`. Copy the style of a nearby landed node.
- To edit an EXISTING node (e.g., add to `## Attempts` of the root or your target), copy it with
  `git show origin/main:<path>`, note that sha, edit only `## Attempts`/frontmatter, land with `GQ_BASE=<sha>` AND `GQ_BASE_PATHS="<those paths>"` (09-18: the lander refuses GQ_BASE without it, and never lets a file you think is new overwrite an existing one).

## 5. Status honesty
- ESTABLISHED only with a complete proof whose inputs are established nodes or verbatim-cited theorems (quote them;
  give arXiv id, version, theorem number). Mark lane-proved sub-lemmas "Not independently reviewed."
- **Anything that would settle G, G', or a named stepping stone** (Aff(Q), U_3(Q), SL_2(Q), GL_2(Q), B_n(Q), …)
  goes to referees first: SendMessage `gq-referee-a` AND `gq-referee-b` with the node paths. Land it meanwhile as
  **OPEN** with the claimed proof under `## Attempts` ("proof claimed, under review"). Flip to ESTABLISHED only
  after both referees PASS, citing their review artifacts. Also ask `gq-lit-arxiv` for a priority check.
- A dead approach is a result: record exactly where it dies (under `## Attempts` of the claim it targeted, or as an
  established obstruction claim). Calibrate every method against O1–O3 before investing in it.

## 6. Landing (land every result and every recorded dead end, as you go)
```sh
printf 'Subject line (<=72 chars)\n\nOne-paragraph body.\n' > $GQ/work/<lane>/msg.txt
[GQ_BASE=<sha> GQ_BASE_PATHS="<existing files you edited>"] $GQ/gqland.sh <lane> $GQ/work/<lane>/msg.txt research/<id>.md research/artifacts/gq-<lane>-x.md
```
The lander refuses: other paths, FRONTIER.md, missing requires/targets/artifacts, id≠stem, model names/ids or
emails anywhere, clobbering someone else's edit. Never write model names or ids in any file.

## 7. Coordination board (instead of the Cairn bus)
- Keep `$GQ/board/<lane>.md` current (≤ 60 lines): **Approach** (family, 3–8-word signature, first falsifiable
  step); **Established** (node ids + landing shas); **Needs** (a statement that would unblock you); **Dead**
  (approach + where it died); **Sparks** (ideas you will not pursue).
- At every checkpoint read the newest boards (`ls -t $GQ/board`) and `git log --oneline -15 origin/main`.
  Before starting a new approach, make sure no board already runs the same idea; if one does, take a genuinely
  different idea, or SendMessage that lane to split the work.
- Take over a `Needs` item or a `Sparks` idea from another board when yours stalls; say so on both boards.

## 8. Messaging
- Load the tool first: ToolSearch `select:SendMessage`. Your final answer text is NOT delivered; only SendMessage is.
- Message another lane only for: a referee request, a lemma it needs, a dependency, a duplicate to split.
- Message `team-lead` only for: a referee-PASSed result, a priority threat, a blocker only the lead can clear,
  and your final report (landed shas, ids, statuses, one paragraph). No progress chatter, no broadcasts.

## 8b. Known priority facts
- Problem 2.7 (G'): Mikaelian, arXiv:2507.04347 (v8 2026-06-03) §1.4, ANNOUNCES (no construction; ref [41]) an explicit
  embedding of GL(n,Q) into a finitely presented, even 2-generator, group via his explicit Higman algorithm. Not simple,
  and not "natural". So G' lanes aim at a NATURAL construction and cite the announcement; G is untouched.

## 9. Credit and scope
- No model names or ids anywhere. The lander adds the commit trailer.
- Stay on G/G' and their stepping stones. Don't touch the Lean tree, manuscripts, or other swarms' files.

## BH SWARM (USER ORDER 09-18 ~08:00: "let's solve Boone–Higman, get massive agent swarm on full solve. named open problems ok too. or cool as fuck stuff")
- Root: `boone-higman-conjecture` (OPEN). The repo already has ~164 boone-higman nodes (equivalences, class results, shell/germ/type (A) routes). READ the relevant subgraph with `git show origin/main:research/<id>.md` (never bin/cairn) BEFORE proposing anything; never re-prove a landed node; grep ids first.
- Lanes are named bh-<topic>. Work dir $GQ/work/<lane>/; board $GQ/board/<lane>.md; artifacts research/artifacts/gq-bh-<lane>-*.md (the lander only allows research/artifacts/gq-*.md).
- Lander: `$GQ/gqland.sh <lane> <msgfile> <paths>` as its OWN command. NEVER run `git fetch`/`git pull` yourself (a chained fetch hung a lane for 2 h on 09-18). Use `git show origin/main:<path>` to read; the sync loop and lander keep refs fresh.
- Deliverables, in order of value: (1) a proof or refutation of BH; (2) BH for a named class not yet on main (say which named problem: BBMZ survey Problem numbers, Kourovka numbers, or a named question in a paper, with the exact source); (3) a sharp equivalence/reduction of BH that changes what must be proved; (4) a clean obstruction that kills a whole route. State status honestly: ESTABLISHED (lane proof) vs refereed; request gq-referee-a (proof gaps) and gq-referee-b (citations/scope) for anything ESTABLISHED that matters.
- Priority: before claiming novelty, check the literature (BBMZ 2306.16356 and its citations, Zaremsky, Belk–Hyde–Matucci, Bux et al., Bleak et al.). Default wording: "no priority claimed".
- Stall rule: after one real attempt without progress, land what you have (Attempts entry with the precise gap) and report to team-lead. Don't message other lanes except through boards, unless you truly need their answer.
- Compute: no local python/cairn/compute. MSI only for fetching sources (arXiv e-prints, library PDFs) and tiny bounded runs (single core, ≤10 min per run, ≤1 h total per lane) that the coordinator approves first; calibrate any search against a planted positive and state a blindness pre-check.
- Report to team-lead via SendMessage when you land or stall; be concise; no acks.
- USER 09-18 ~08:40: "get everything to main continuously, no need for referee passes". Land every result, attempt, and correction to main as soon as it is written (small, frequent landings), and never wait on a referee. Referee reviews are optional extras, not gates: do not request them unless a claim is load-bearing for BH itself. Status lines still say honestly "lane proof, not reviewed".
- Unowned named problems are listed in $GQ/board/UNOWNED.md; a free lane may claim one there.
- FREE LANES (USER 09-18 ~09:10: "give agents more freedom on how they go about things"): lanes named bh-free-* (and any lane told it is free) choose their own sub-question, method and pivots inside their seed theme, or anywhere in BH / named problems if fully free. Post your chosen direction on your board early (one line, updated when you pivot) so others avoid duplication; read bh-map's map, bh-lit's survey (d7b638fef) and the boards first. Pivot freely when a direction stalls; the stall rule becomes "land what you have, then pick the next best direction yourself" (report to team-lead only for significant landings or when you finish).
- EDITING AN EXISTING NODE (09-18 clobber incident): record SHA=$(git rev-parse origin/main), copy the file with `git show $SHA:research/<id>.md`, edit that copy, and land with GQ_BASE=$SHA GQ_BASE_PATHS="research/<id>.md". Never edit a copy taken from the working tree or an older read. The lander now refreshes origin/main itself before its clobber guard.
