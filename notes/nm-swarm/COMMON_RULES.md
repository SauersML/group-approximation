# COMMON RULES — non-MF verbatim unconditional formalization swarm (lead: session nonsofic-existence-41, 2026-09-11)

NM = /private/tmp/claude-501/-Users-user-nonsofic-existence/77122910-de5a-4e59-a488-7cea550292c5/scratchpad/nm
Repo = /Users/user/nonsofic_existence (SHARED working tree; other lanes and sessions edit it concurrently)
Manuscript = `non_mf_groups_exist.tex` at origin/main (2022 lines, last edit 73c867c5b). ONLY this paper.

## USER ORDERS (verbatim intent; violations get the lane stopped)
- "Verbatim unconditionally formalize entire non-MF manuscript in Lean. all steps, statements, etc."
- "no literature inputs ever" — every cited theorem a printed sentence relies on (Hull, Osin, DGO, GO,
  FFF, AGP, Khanh–Thanh, GHW, Korchagin, Elek–Szabó, Blackadar–Kirchberg, Menal–Moncasi, Preusser, ...)
  gets PROVED in Lean.  Never a hypothesis, structure, class or Prop binder standing for a cited
  result in any endpoint.  Only `propext`, `Classical.choice`, `Quot.sound` in `#print axioms`.
- "lets get everything on main constantly" / "always commit and push regularly" / "dont lose work":
  land EVERY green increment IMMEDIATELY with nmland.sh.  Never sit on green unlanded work.  Keep a
  copy of every file you edit under `$NM/backup/<lane>/` after each edit cycle.
- MSI only, via the msi wrapper and the scripts below.  Do not run code or build locally (reading,
  grep/rg, sed, editing, git read-only commands are fine; emitting/reading ASM/IR/PTX is allowed).
  Do not spam jobs; get signal fast (probe small module sets, split big modules); never tolerate slow
  compiles — if a probe is slow, split the file or shrink the closure.  Never use /tmp on MSI nodes.

## Build: ONLY `bash $NM/nmprobe.sh <lane> <GroupApproximation.Module> [...]`
1. Your owned files are listed in `$NM/lanes/<lane>.files` (one repo path per line, e.g.
   `GroupApproximation/Manuscript/NonMF/Foo.lean`).  Add every NEW file you create and every EXISTING
   file you edit to that list BEFORE probing.  The probe builds origin/main (current tip) + exactly
   those files; nothing else from the shared tree reaches the build.  Remove a path from the list when
   you abandon it.
2. Run probes with Bash `run_in_background: true` and read the output file when notified; keep
   authoring meanwhile.  One probe per lane at a time.  NEVER kill a probe (the remote build keeps
   the lock).  Exit 5 / `PROBE DEFERRED` = your clone is still being prepared (base warm build + copy,
   first ~1–2 h): author blind meanwhile, retry after ~15 min of work.
3. A real green: `PROBE GREEN` AND a `BUILT <module>` line for every module you changed.
   `mentioned-not-built` on a changed module = not evidence.  Probe the modules you changed plus the
   direct importers of any existing module whose statements you changed.
4. Warnings are errors (`-DwarningAsError=true`): no unused variables/simp args, no deprecated names.

## Land: ONLY `bash $NM/nmland.sh <lane> <msgfile> <path> [...]`
5. It lands exactly the bytes of your latest green probe (edit after green ⇒ re-probe), refuses
   sorry/admit/axiom/native_decide, dangling imports, the root file.  Commit message file: first line an
   imperative summary (what is proved), blank line, a short body.  The script appends the attribution.
6. Never `git add/commit/push/reset/stash/revert/amend/checkout/branch/worktree` yourself.  Never edit
   `GroupApproximation.lean` (the lead wires landed modules into the root in waves and tells you).
   Never edit the manuscript tex; send tex issues to the lead.  Never edit another lane's files: ask
   the lead.  Never touch LIX/CharClass in-flight files unless you are `rescue-lix`.

## Lean rules
7. New module: check the target path does not exist (`ls`), and its name differs from every existing
   module by more than letter case (APFS is case-insensitive).  Never rename/move/delete existing modules.
8. Grep before declaring anything missing: `rg -n '<name>' GroupApproximation` AND
   `git grep -n '<pat>' origin/main -- GroupApproximation` (the shared tree has unlanded peer files;
   origin/main is what the probe sees).  A `private` hit cannot be reused.  Grep for PRODUCERS of a Prop,
   not only its declaration.
9. VERBATIM: statements carry the manuscript's literal objects at the printed generality (no weakening,
   no extra hypotheses, no "at n = 4 only" when the paper says every n).  Proof-step carriers follow the
   printed route; a different route is recorded as `partial` with the reason, never as formalized.
   Quote the printed sentence (tex line + \label) in the docstring.
10. Endpoints closed: quantifiers inside the proposition, never a literature package as a binder.
    GATE TRAP: `#audit_closed_axioms` REJECTS a theorem whose type is syntactically `∀ ...`.  Spell every
    endpoint as `def PrintedFoo : Prop := ∀ (G : Type) [Group G], P G` plus `theorem printedFoo : PrintedFoo`.  Intermediate lemmas may take ordinary mathematical
    hypotheses.  Scaffolds may land with an OPEN LEAF only as an explicit hypothesis of an intermediate
    lemma (never `sorry`), and you then prove the leaf.
11. No `sorry`, `axiom`, `native_decide`, `opaque` for math, `unsafe`, `implemented_by`.  Put
    `#audit_closed_axioms <decl>` (from `GroupApproximation.Meta.AxiomGuard`) after each endpoint and
    every `manuscriptSentence_*` theorem; the module's closing audit block must list every endpoint.
12. Read `/Users/user/.claude/projects/-Users-user-nonsofic-existence/memory/MEMORY.md` ("Lean gotchas")
    and open the linked file for any trap you hit.  Mathlib is PINNED at 81a5d257 (lake-manifest,
    tag v4.32.0).  The local repo `/Users/user/mathlib4` is checked out at a DIFFERENT commit (8eb5ccdf):
    never trust `rg` over its working tree.  Check names AT THE PIN:
    `git -C /Users/user/mathlib4 grep -n '<pat>' 81a5d257 -- Mathlib` and
    `git -C /Users/user/mathlib4 show 81a5d257:Mathlib/<path>`; never checkout/fetch there.
    At the pin `ContinuousLinearMap.{mul,smul,sum,one,zero,sub}_apply` are deprecated aliases (errors
    under warningAsError): use `mul_apply_eq_comp`, `smul_apply`, `sum_apply`, `one_apply_eq_self`, ...
13. Big developments: many small modules (≤ ~600 lines), each probed and landed as soon as green.

## Census rows (sentence-level grading)
14. After `LANDED <sha>` only, append rows to `$NM/rows/<lane>.tsv`:
    `LINE:<texline><TAB><status><TAB><fully.qualified.decl ...><TAB><note incl. LANDED sha>`
    statuses: formalized | definition | structural | attribution | provenance | partial | open.
    `formalized` only for a closed declaration proving exactly the printed sentence along the printed
    route.  The `census` lane merges rows into `metadata/NON_MF_SENTENCE_MAP.tsv`.

## Reporting
15. Load the tool once: ToolSearch `select:SendMessage`.  Report with
    `SendMessage(to: "main", summary: <5–10 words>, message: <full report>)` (if "main" errors, use
    to: "nonsofic-existence-41").  Report after every landing (SHA, modules, declarations), on any
    blocker, and at least every ~90 minutes: probe status, the EXACT remaining residual statements, and
    what you are doing next.  Plain final text is also returned to the lead when your turn ends, so end
    your turn with a complete report; the lead resumes you with SendMessage.
16. Do not stop at a verdict: progress is landed theorems.  If your scope is finished, say so and ask
    for more.  If a statement you need belongs to another lane, ask the lead (do not build it).
17. Refuted/over-strong statements: if you find an admitted/cited statement is false as stated,
    prove the refutation, land it, and report the corrected statement to the lead immediately.

## 18. USER ORDER 19:25: "no hold, get everything into main asap"
- nmprobe records COMPILED evidence: only overlay files that actually compiled in that build
  (olean newer than source), EVEN WHEN THE OVERALL PROBE FAILED. Land every compiled file at once.
- NEW .lean files that have not compiled yet (not on origin/main): land NOW with
  `NM_UNVERIFIED=1 bash $NM/nmland.sh <lane> <msg> <paths>` (not wired, so the root stays green);
  re-land them the normal way once they compile.
- EDITS to modules that already exist on origin/main and have not compiled: preserve NOW with
  `NM_ATTIC=1 bash $NM/nmland.sh <lane> <msg> <paths>` (text copies under attic/inflight/<lane>/);
  land the real edit after it compiles.
- Nothing lives only in the shared tree or a backup. Re-land after every edit cycle.

## 21. USER ORDER 22:45: "we MUST commit and push after LITERALLY EVERY EDIT. an edit NOT PUSHED AND COMMITED TO
##     MAIN is UNSAVED. do not clobber other work or overwrite when u push though"
- After EVERY Edit/Write of a repo file, before probing or anything else, land it at once:
  - new GroupApproximation .lean, or your OWN earlier unverified file not reachable from the root:
    `NM_UNVERIFIED=1 bash $NM/nmland.sh <lane> <msg> <paths>` (nmland now allows re-landing your own unwired files);
  - an edit to a module reachable from the root or compiled on main: `NM_ATTIC=1 ...` (attic text copy), and the
    real module after its green probe;
  - non-Lean files you own (notes, reports): plain nmland.sh.
- Census rows: keep `metadata/nm-census-rows/<lane>.tsv` IN THE REPO (copy from `$NM/rows/<lane>.tsv`) and land it
  after every append; land your report as `notes/nm-swarm/reports/<lane>.md` (LIX lanes:
  `notes/lix-stronger-lane-reports/<lane>.md`) after every edit. Never put MSI user/host/group paths in landed files.
- NO CLOBBERING (nmland enforces): a path whose origin version was changed by anyone but you after your copy was
  made is REFUSED. Then `git show origin/main:<path>`, merge their change into your copy, and re-land with
  `NM_BASE=$(git -C /Users/user/nonsofic_existence rev-parse origin/main)`. Never force, never overwrite peer work,
  never land a file you do not own (ask the lead).

## 20. USER ORDER 21:45: "agents dont need their unique compute ... we dont need to compile same code a billion
##     times ... dont do unnecessary msi compute. kill what u dont need"
- Every probe now uses ONE shared Lake artifact cache (LAKE_ARTIFACT_CACHE, content-addressed by input hash, in
  `nm/lake-cache`): a module compiled in any clone is restored, not recompiled, in every other; a restore counts
  as COMPILED evidence (same input hash).
- Clones are SHARED (several lanes per clone; `$NM/lanes/<lane>.clone`); waiting on the clone lock is expected.
- Probe ONLY the modules you changed since your last green, batched into one probe. Never re-probe unchanged
  files; never add peers' already-compiled modules to your overlay "for evidence"; no speculative or duplicate
  probes; no waiter loops that resubmit jobs; kill your own stale waiters/jobs. `NM_CPUS` stays 8.
- Model tests: seconds, on acn112, never a SLURM job unless the lead approves.

## 19. Fleet traps collected 09-11 evening
- `map_sub`/`map_mul` on a `→+*` into a heavy corona type can time out in AddMonoidHomClass search even with
  explicit args: use `RingHom.map_sub` etc.  `#audit_closed_axioms` rejects ANY theorem with binders; use
  `#audit_axioms` for lemmas.
- `attribute [local reducible]` on `InnerGRegion.diagram` / `MapCollapse.replaceGRegion` fails ("affects term
  indexing"); darts of a collapse spelled `R.diagram.toCombMap.Dart` make `rw` through `Subtype.val` fail
  ("not type-correct under instances transparency"): wrap the projection in a def and state lemmas through it.
- `open HullSC Embedded` opens `HullSC.Embedded`, not `VanKampen.Embedded`: use the full namespace.
- Mathlib module `Mathlib.Analysis.SpecialFunctions.Pow.NNRpow` does not exist at the pin (it is `Pow.NNReal`);
  a file without the Real import turns ℝ into an auto-bound implicit silently (add Data.Real.Basic).
- `variable (U ι V) in def f` keeps declaration order: explicit-argument order follows the variable declarations,
  not the `in` list.
- `noncomm_ring` leaves `-1 • x` terms on `Module.End k (U × (ι → V))` goals with subtraction: use
  `rw [sub_mul, mul_sub]` then `abel`.
- `rw [sub_self]` / `sub_mul` / `neg_sub` can find NO occurrence in `FiniteRank (rho x - rho y)` over
  `Module.End k (List (Fin d) →₀ k)`: the elaborated subtraction is not the ring one at reducible transparency. Use
  generic congruence lemmas stated on an arbitrary `Module.End k V`, applied with `exact` (leavitt-k1).
- Unicode subscript minus/plus (`hc₋`, `hc₊`) are NOT identifier characters: the parse breaks and everything below
  is silently unelaborated. `push_neg` is deprecated at the pin: `push Not`.
- `induction … using closure_induction` auto-reverts hypotheses mentioning the variable: `clear` them first.
- `map_continuous` on a `→⋆ₐ[ℂ]` needs `open scoped CStarAlgebra` (`instContinuousLinearMapClassComplex` is scoped). `z • c` on a sequence type over a subtype-`abbrev` can time out in instance search: add the Nonempty binders and a type ascription. `zpow_neg` is ambiguous under `open Matrix`.
- `even_zero` does not exist at the pin: it is `Even.zero` (to_additive of `IsSquare.one`).
- `autoImplicit` is ON in this repo: a missing import appears as "Function expected … unknown identifier
  treated as implicitly bound", not as "unknown identifier". `push_neg` → `push Not`;
  `ContinuousLinearMap.add_apply` → root `add_apply`; `List.take_append_eq_append_take` → `List.take_append`.
