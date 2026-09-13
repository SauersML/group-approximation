# Gottschalk team rules (2026-09-12, lead: session nonsofic-existence-c9)

## Mission

Decide Gottschalk's surjunctivity conjecture completely: every group, every finite alphabet,
every injective cellular automaton on the full shift is surjective, OR some group carries an
injective non-surjective one. Either answer counts. The Cairn goal is
`gottschalk-surjunctivity-conjecture` (refuted_by `leavitt-unit-group-nonsurjunctive`).

User orders: "get agent team to fully solve Gottschalk", "commit and push to main regularly",
"do not use heavy compute", "wire into Cairn continuously", and, repeated: "all agents MUST
contribute to cairn and commit and push to main no clobbering others continusouly".

**So:**
* Every lane lands Cairn nodes on main continuously, verifiers and steward included.
* Every edit lands the moment it is made; nothing is held until finished.
* A lane with nothing on main after 30 minutes is failing the order. Land the current state
  (open claims with Attempts, obstructions with invalidates, routes, and the artifact they cite).
* Never clobber: REFUSE means merge onto their version.
* You are a lane, not the coordinator: never launch agents, never address the user.

You own your problem. Any approach, the opposite answer included, and pivot whenever you find
something better. Your lane's starting point is a start, not a fence. Several lanes overlap on
purpose; SendMessage the neighbours you need.

## WAVE 6 (~18:40 CDT Mac clock; swarm drained to ~15; not solved)

Both counterexample routes are now "the Leavitt unit group has no nontrivial weakly finite char-p representation"
(pending verification of Theorems B, C and W). Everything outside E⋊V comes from one transvection x (G_3 = ⟨V, x⟩).

| group | lanes |
|---|---|
| chain verifier | w6-vf-chain (Theorems C, B, W; reflection ideal; flattening; certificate criterion) |
| multi-letter factors | w6-mismatch-c3, w6-mismatch-c2 (verifier w4-vf-gate) |
| direct Kaplansky pair | w6-wf-stage1-a (one transvection), w6-wf-stage1-b (Hadamard, SD16, GL2(F3)) (verifier w4-vf-linear-b) |
| upgrade | w6-upg-separate (do two-root certificates separate; w4-vf-linear-b) |
| V extension | w6-v-extend (extend V rank functions to G_3; w4-vf-gate) |
| construction side | w6-wf-construct (stably finite targets for R^x or G_3; w4-vf-linear-b) |
| free | w6-free-neg-d (w3-vf-nonlinear), w6-free-pos-d (w4-vf-positive-b) |

## WAVE 5 (~17:10 CDT Mac clock; swarm refill after ~15 finishes; not solved)

The char-3 gate is the one tied to the goal. With family UPG's state upgrade, "G_3 has no nontrivial char-3 rank model"
gives a Gottschalk counterexample. Restricting to E⋊V (which contains z) reduces that to anti-central models of E⋊V.

| group | lanes |
|---|---|
| char-3 gate (verifier w4-vf-gate) | w5-c3-signed-thompson, w5-c3-descent, w5-c3-submult |
| binary gate | w5-v-infinite-order (verifier w3-vf-linear; V gate implies the R^x gate) |
| chain audit | w5-red-upg (adversarial audit of the UPG counterexample chain) |
| binary upgrade | w5-binary-upg (verifier w4-vf-linear-b) |
| other | w5-rgr-p (w4-vf-linear-b), w5-quant-surj (w3-vf-positive), w5-laminar-cycle (w4-vf-linear-b) |
| strategy and free | w5-strategist-synth, w5-free-neg-c (w3-vf-nonlinear), w5-free-pos-c (w4-vf-positive-b) |
| rank-function regularity | w5-regular-rankfn (verifier w4-vf-gate) |
| V gate, nonamenable configurations ~18:15 | w5-v-nonamenable (w3-vf-linear) |
| synthesis gaps ~18:25 | w5-sub-fock (SUB multi-letter input: Fock Toeplitz quarter; w4-vf-gate), w5-inf-c (INF for every group; w4-vf-positive-b) |
| balance seed ~18:20 | w5-two-patch (smallest open unbalanced ternary rule; w3-vf-nonlinear) |
| single decisive binary target ~18:05 | w5-wf-binary (T = fF_2[R^x]f has no nonzero weakly finite image; equivalent to the full binary corner; w4-vf-linear-b) |
| single decisive ternary target ~18:00 | w5-wf-obstruct (`ternary-anti-central-summand-has-no-weakly-finite-image`: equivalent to the full corner, so it refutes Gottschalk with no rank functions; w4-vf-linear-b) |
| refills ~17:50 | w5-c3-outside (link 1 outside E⋊V, w4-vf-gate), w5-upg-flatten (link 2 over S_-, w4-vf-linear-b) |
| refills ~17:35 | w5-commutant-distort (SUB, w4-vf-gate), w5-cohn-lef (w4-vf-gate), w5-bal-distinct (w3-vf-nonlinear), w5-integer-marker (w3-vf-nonlinear) |

w3-vf-positive has finished. Its remaining lanes (w4-three-point, w5-quant-surj, w5-free-pos-c, w4-linsofic-surj) go to
w4-vf-positive-b. gkland.sh lint (installed ~17:30) now refuses nodes with no `rg: 2`, no `title:`, and routes with no
`requires:`.

## WAVE 4 (~15:40 CDT Mac clock; user: "solve"; not solved)

Leverage: Gottschalk ⟺ every injective automaton has a BALANCED local rule (w3-inf-a, f18605afa1).
This holds because bijective automata preserve the uniform measure over every group.

| group | lanes |
|---|---|
| balance | w3-bal-design, w3-bal-prove, w4-bal-census, w4-window-boundary |
| negative | w4-binary-cyclic, w4-hadamard-f3, w4-cohn-gram, w4-kap-join, w4-clifford-df, w4-clifford-nonlinear, w4-measurable-2, w4-free-neg-b |
| positive | w4-metric-ultra, w4-simple-q, w4-free-pos-b |
| strategists | w3-strategist-neg, w3-strategist-pos, w3-strategist-gate |
| family R4 (lead w3-strategist-gate, verifier w4-vf-gate) | w4-r4-orth, w4-r4-complete, w4-r4-corner, w4-r4-adversary, w4-r4-approx, w4-heisenberg, w4-gate-descent |
| family SUB (lead w3-strategist-gate, verifier w4-vf-gate; target leavitt-disjoint-cylinder-defects-strictly-submultiplicative) | w4-sub-halving, w4-sub-adversary, w4-sub-weyl, w4-cohn-el3 (Cohn-coefficient EL3 identity) |
| family UPG (state upgrade: K0 state on S_- => nontrivial char-3 rank model; with gate "No" gives a counterexample) | w4-upg-state, w4-upg-kill (verifier w4-vf-linear-b), w4-upg-audit (verifier w4-vf-gate) |
| gate plans | w4-defect-cov (verifier w4-vf-gate), w4-tensor-rankfn (verifier w3-vf-linear) |
| hosts | w4-deligne-twisted (verifier w4-vf-linear-b), w4-bal-rigid (verifier w3-vf-nonlinear), w4-three-point (verifier w3-vf-positive), w4-lamp-closure (verifier w3-vf-nonlinear), w4-clifford-copy (verifier w3-vf-nonlinear) |
| refills | w4-kap-triangular (verifier w4-vf-linear-b), w4-z3-rotation (verifier w3-vf-nonlinear), w4-radu-f2 (verifier w4-vf-linear-b), w4-gate-v2 (verifier w3-vf-linear), w4-char3-construct (verifier w3-vf-linear), w4-linsofic-surj (verifier w4-vf-positive-b), w4-rankfn (verifier w3-vf-linear), w4-trace-state (verifier w4-vf-linear-b), w4-deligne-projective (verifier w4-vf-linear-b), w4-clifford-complete (verifier w3-vf-nonlinear), w4-dihedral-marker (verifier w3-vf-nonlinear), w4-jacobson-radical (verifier w3-vf-linear), w4-fock-model (verifier w3-vf-linear) |
| verifiers | w4-vf-linear-b (corner-f4, corner-cohn-a/b, free-neg Clifford, w4 linear lanes), w4-vf-positive-b (inf-a, bern-window, bal-prove, window-boundary), w4-vf-gate (family R4) |

Wave 3 lanes that finished: corner-cohn-a, corner-cohn-b, corner-module, corner-f4, kap-kernel, measurable,
free-neg, inf-a, inf-b, bern-window, products, weaksofic, simple-direct, free-pos, v-linear.

## WAVE 3 (15:00–15:22 CDT Mac clock; user: "u have barely any agents, why? did u solve it already?"; not solved)

Refill the swarm and keep it full. Lanes are prefixed `w3-`.

| group | lanes |
|---|---|
| negative | w3-corner-cohn-a, w3-corner-cohn-b, w3-corner-module, w3-corner-crossed, w3-corner-f4, w3-kap-visible, w3-kap-kernel, w3-v-linear, w3-measurable, w3-lattice, w3-nonformal, w3-free-neg |
| positive | w3-inf-a, w3-inf-b, w3-bern-window, w3-products, w3-weaksofic, w3-stable-simple, w3-simple-direct, w3-deligne, w3-alphabet, w3-free-pos |
| gates | w3-gate-char3, w3-gate-bridge-a, w3-gate-bridge-b, w3-gate-construct, w3-gate-v |
| verifiers | w3-vf-linear (corner, kaplansky, gates), w3-vf-nonlinear (nonlinear, measure, lattices, V), w3-vf-positive (positive side) |

Also still running: gk-gate-compress, gk-n-klein, gk-cairn-steward.

Hard cap for every lane: no single tool call or message over about 300 lines. Land artifact sections one at a time.

## ALWAYS LAND (user, repeated ~13:00 CDT)

"they should all contribute to Cairn, commit and push to main constantly, always commit approaches,
solutions, ideas, refutations, etc."

Land everything, not only finished theorems:

| what you have | what you land now |
|---|---|
| an idea you are pursuing | an open claim with `## Attempts`, or an Attempts entry on the node it bears on |
| an approach that dies | an obstruction claim with `invalidates:` on its route, or an Attempts line saying exactly where it dies |
| a refutation | the negation as its own claim, plus its `-proof` route |
| partial progress | an artifact section, plus the open claim that cites it |
| a solution | artifact, claim, and route (decision-level claims stay OPEN until the family verifier passes them) |

Land within minutes of forming it, with gkland.sh. Hold nothing in your head or your scratch dir.
Never clobber: REFUSE means gkshow, merge, then GK_ACK. A lane with nothing on main is failing the
order.

## SWARM (12:40 CDT; user: "u barely have agents, let's get massive swarm on this")

This supersedes every older roster below. You are ONE lane. You are NOT the coordinator:
- write no fleet summaries;
- send no rule reminders to other lanes;
- launch no agents.

**Frontier at launch (read these nodes first):**
- **Ternary lift, the most concrete counterexample target:** `ternary-anti-invariant-swap-corner-is-full`.
  - F_3[G_3] = S_+ x S_- with G_3 = L_(F_3)(1,2)^x.
  - c e b = 1 already holds in R with b = s0+s1, c = 2(t0+t1). Lifting it along S_- -> R to
    c' e_- b' = eps_- refutes Gottschalk.
- **Binary lifts:**
  - `left-invertible-lift-of-s0-in-leavitt-group-algebra` (V);
  - `leavitt-evaluation-kernel-unitization-not-directly-finite` (I);
  - normal forms in `leavitt-inverse-defects-are-visible-or-invisible`.
- **Projective Klein target:** `projective-ternary-klein-idempotent-is-full`. PG is nonsofic (`projective-leavitt-unit-groups-mod-scalars-are-nonsofic`).
- **Rank gate:**
  - `binary-leavitt-unit-group-is-f2-linear-sofic` and `f2-linear-sofic-groups-kill-rigid-compression-defects`;
  - (T) gives NO rank rounding over finite fields (`kazhdan-group-rank-models-admit-no-expander-decomposition`).
- **Entropy:**
  - `leavitt-units-have-zero-rokhlin-entropy-supremum` (a finite deficit certificate suffices; median matching is refuted);
  - `bernoulli-rokhlin-maximal-on-fg-simple-kazhdan-groups`;
  - `every-injective-ca-preserves-uniform-bernoulli-measure`;
  - `end-fixing-tree-symmetries-carry-strict-automata`: unimodularity is essential.
- **Design filters, all landed:**
  - nonsofic forward core;
  - triangular tables;
  - holonomy normal form;
  - amenable decoder memory forces surjectivity;
  - at least two independent cycles, under Pestov 4.10;
  - measure distortion;
  - permanence-closure evasion;
  - a certificate must live in ONE decidable host (Pi^0_2 dichotomy).
- **Reductions:** f.g. simple Kazhdan hosts suffice (`gottschalk-reduces-to-fg-simple-kazhdan-groups`). Tower V <= R^x <= d-ary A^x. Every combinatorial normal-form claim is equivalent to the goal.

**Families** (the verifier re-derives before any decision-level `-proof` route lands):

| family | lanes | verifier |
|---|---|---|
| L: linear lifts and the rank gate | gk-kdf-structure (lead lane), gk-l3-kernel, gk-l3-units, gk-l3-corner, gk-l3-obstruct, gk-l3-free, gk-l2-visible, gk-l2-invisible, gk-lp-hosts, gk-l-gate-neg, gk-l-gate-pos | gk-vf-linear |
| N: nonlinear designs and entropy certificates | gk-invariant-output (lead lane), gk-n-klein, gk-n-twocycle, gk-n-defect, gk-n-boolean, gk-n-ae-decoder, gk-n-highalpha, gk-n-thompson-v, gk-n-ff | gk-vf-nonlinear |
| P: positive | gk-p-inf-cost, gk-p-inf-f, gk-p-inf-kazhdan, gk-p-inf-wild, gk-p-bernoulli-mass, gk-p-bernoulli-popa, gk-p-bernoulli-ergodic, gk-p-simple-direct, gk-p-products, gk-p-tails | gk-vf-positive |
| free | gk-free-neg, gk-free-pos, gk-free-wild | by topic |
| F: formalizability (added ~14:00; user: "when u get leverage... attack it with agents and exploit") | gk-free-neg (lead lane), gk-fz-bennett, gk-fz-obstruction, gk-fz-decompose, gk-fz-counter, gk-fz-alphabets, gk-fz-kari, gk-fz-strict. TARGET MOVED ~14:40: the unstabilized form is refuted; aim at `injective-binary-automata-are-stably-formalizable` / `prime-field-left-inverse-pairs-are-stably-formalizable` | gk-vf-nonlinear |
| R: rank rigidity of EL_3 (added ~14:20; target `el3-rank-models-factor-through-ring-rank-models`, payoff: R^x not F_2-linear sofic, the first non-linear-sofic group) | gk-l-gate-neg (lead lane), gk-rk-unipotent, gk-rk-extensions, gk-rk-composition, gk-rk-free, gk-ri-nofd, gk-ri-selfsim, gk-ri-counter; wave 2 (~15:40): gk-gate-compress, gk-gate-nonsofic. Other wave-2 lanes: gk-l3-state (family L, K_0 states on S_-), gk-fz-catalyst (family F, catalytic ancillas). ~15:00 the gate is EQUIVALENT to `rank-models-of-el3-satisfy-the-two-root-identities` (N_23 N_12 = 0 in char 2); proofs must use coefficient families with no f.d. representation | gk-vf-linear |
| graph | gk-cairn-steward (only `cairn check`), gk-dedup (duplicate reconciliation), gk-archive (knowledge digests into Attempts) | gk-verify-pos (senior, standby for decisions) |

**Swarm coordination:**
- At start, SendMessage your family siblings once: your plan in at most five lines, so you diverge
  instead of duplicating. Exchange obstructions the moment you find them.
- Before authoring a node, check `git log "$T" -- research/` for the same topic landed in the last
  hour. If it is there, reuse it.
- Messages to the lead go to `main`, not to a session name. Send only decisions and incidents.
- A claimed decision (the conjecture, any host's surjunctivity, any lifting problem) lands as OPEN
  with the candidate proof. SendMessage your family verifier and `main`.
- Push contention will be heavy. If gkland prints GAVE UP, rerun it; nothing is lost.

## Compute: none that is heavy

* On this Mac only: git, grep, reading and editing files, and the two gk scripts. No Python,
  Lean, TeX, SAT, or scripts of your own. Do not Read multi-page PDFs locally.
* On MSI (wrapper `/Users/user/msi-node/msi`), only a tiny exact check of a finished
  certificate: one core, at most 10 minutes, at most 2G, via the shared checker in
  `/projects/standard/hsiehph/sauer354/nonsofic-certificates/current/experiments/nonsofic-certificates/`
  (README in `experiments/nonsofic-certificates/README.md`). No searches, sweeps, enumerations,
  or Lean builds anywhere. At most one MSI job per lane at a time, never left running.
* `cairn check` runs only in `gk-cairn-steward`, on MSI.
* Do not start a background job and end your turn.

The work is mathematics on paper. Write proofs and constructions, not programs.

## Saving: land every edit on main, at once

An edit that is not on main is unsaved. Each coherent edit (a node, an artifact, a correction)
lands immediately with

```bash
GK=/private/tmp/claude-501/-Users-user-nonsofic-existence/0a930a1d-0cf3-4aa0-b91a-b8bfce7d68c7/scratchpad/gk
bash $GK/gkland.sh <your-lane> <msgfile> <path> [<path>...]
```

* Paths are repo-relative. `path@/abs/file` lands the content of `/abs/file` at `path`.
  `path@DELETE` removes a path. It is guarded like an overwrite (`GK_ACK` for someone else's
  blob), and the lint refuses while any remaining node names the deleted id. (10:35 fix: a SHA
  containing "403" no longer reads as an auth failure.)
* Write the commit message to your own file first (`$GK/lanes/<lane>/msg-<n>.txt`). Subject in
  the house style ("Prove ...", "Record ...", "Refute ..."), a short body saying what the
  mathematics is, then the two trailer lines from the attribution reminder:
  `Co-Authored-By: Claude Code <noreply@anthropic.com>` and
  `Claude-Session: https://claude.ai/code/session_018da4ZMvDEshSvGp3YdQgZQ`.
* Read the script's output. `LANDED <sha>` means saved. `REFUSED` (exit 2) means someone
  changed that path: fetch main's copy with `bash $GK/gkshow.sh <path> $GK/lanes/<lane>/<file>`,
  merge your change into it, and rerun with `GK_ACK="<path>=<blob printed by gkshow>"`.
  `LINT FAILED` (exit 3) means a node would redden the graph; fix it. `GAVE UP` means rerun.
* New files: write them at their final path in the shared checkout
  `/Users/user/nonsofic_existence/`, then land at once. Keep a backup copy in
  `$GK/lanes/<lane>/` until landed.
* Edits to existing files (including your own after a peer touched them): fetch main's copy
  with gkshow, edit that copy in `$GK/lanes/<lane>/`, land with `path@/abs/copy` plus `GK_ACK`.
  Never overwrite someone else's disk copy in the shared checkout; it may be their unsaved work.
* Forbidden: `git add`, `git commit`, `git reset`, `git stash`, `git checkout -- <file>`,
  branches, worktrees, rebase, merge, amend, revert, force-push. The script is the only way to land.
* Read main at its live tip, never the stale local HEAD. In zsh brace refspecs:
  `T=$(git ls-remote origin refs/heads/main | cut -f1); git cat-file -e "${T}^{commit}" || git fetch -q origin "$T"; git show "${T}:research/<id>.md"`.
  Before authoring a node: `git ls-tree -r --name-only "$T" research/ | grep <topic>` and
  `git status --porcelain research/` (a peer may be mid-write).

## Cairn: wire continuously

Everything you learn goes into the graph as you learn it, as graph structure, not loose prose.

* Results: a claim plus its `<id>-proof` route (`requires: []` for a complete direct proof, or
  the claims it uses). The proof goes in `research/artifacts/<topic>-2026-09-12.md`, landed in
  the same landing as the nodes that cite it, or before them.
* Reductions and equivalences: routes whose `requires:` name claims. An equivalence is two
  routes; say so in both bodies.
* Obstructions and dead ends: an established claim carrying `invalidates: [<route ids>]`, and
  the dead route kept. A dead route with no invalidator proves its target: never land one.
* Open holes: an open claim with an `## Attempts` section (at least one approach and where it dies).
* Refutations: land the negation as its own claim.
* Mechanics: ids at most 64 characters, equal to the filename. `requires`, `target`,
  `distinct_from`, `refuted_by` name CLAIMS, and `invalidates` names ROUTES. Single-line flow
  lists or block lists, never wrapped flow lists. Only the author writes `distinct_from` on
  their own node. Reuse existing nodes; the region already holds about 133 Gottschalk,
  Kaplansky and stable-finiteness nodes.
* Update the goal node's `## Attempts` only through gk-cairn-steward (SendMessage it one
  paragraph), so twenty lanes do not race one file.
* Traps to avoid: restatement dressed as reduction; a hypothesis that silently lapses; a proper
  subshift in place of the full shift; injectivity on finite configurations only (that is
  pre-injectivity, Moore–Myhill territory); left-versus-right memory conventions
  (`tau(x)(g) = mu((x(g m))_m)`); reading a source's choice as a requirement.

## Claiming a decision

If you believe you have decided the conjecture, or the surjunctivity of any specific nonsofic
group, land the artifact at once and the claim as OPEN with the candidate proof in `## Attempts`.
Then SendMessage `gk-verify-neg` or `gk-verify-pos` with the artifact path. Add the `-proof`
route only after the verifier's independent re-derivation passes. Also SendMessage the lead
(`nonsofic-existence-c9`) a short note.

## Messaging

* Team lanes by name (below). Do not message other sessions. The peer coordinator's lanes
  (`gottschalk-positive-host`, `gottschalk-leavitt-ca`, `kdf-leavitt-certificate`, `lit-scout`)
  are not reachable; read their work in `git log "$T" -- research/` and build on it through Cairn.
* Your final message is your report to the lead: landed SHAs, Cairn ids, what is proved, what
  is refuted, what is open and where it dies.

## Combined team (~10:45 CDT; user: "combine agents, make sure no work lost")

| lane | owns |
|---|---|
| `gk-kdf-structure` | Kaplansky for R^x, construction and obstruction (absorbs gk-kdf-lift) |
| `gk-invariant-output` | every nonlinear counterexample construction (absorbs gk-design-group, gk-defect-automaton) |
| `gk-other-hosts` | every host, both directions: R^x, V, U, simple Kazhdan hosts (absorbs gk-leavitt-positive, gk-fixed-host) |
| `gk-rokhlin` | analytic positive routes: entropy, measure, decoder fiber, observables (absorbs gk-decoder-fiber, gk-observables) |
| `gk-logic` | combinatorial and logical routes: three-factor normal form, finitary core (absorbs gk-three-factor) |
| `gk-verify-pos` | the single verifier, both sides (absorbs gk-verify-neg) |
| `gk-cairn-steward` | graph health, cairn check, goal-node Attempts |

Absorbed lanes land every leftover file, hand off by SendMessage, and end. Stopped at the usage
limit and resumable by SendMessage later: gk-fixed-host, gk-observables (files rescued at
5ae3e5bd69), gk-defect-automaton (wrote nothing), gk-three-factor (all written files on main; an
unwritten theorem region remains in its transcript).

## Original roster (superseded by the table above)

Negative side (find the automaton):
* `gk-kdf-lift`: Kaplansky direct finiteness over `F_2[R^x]`, `R = L_(F_2)(1,2)`, by lifting a
  Leavitt one-sided inverse along the linear extension `F_2[R^x] -> R` of `R^x ⊂ R`. Anchors:
  `leavitt-unit-group-algebra-not-directly-finite`, `leavitt-group-algebra-not-stably-finite`,
  `leavitt-direct-finiteness-failure-from-left-invertible-lift`,
  `direct-finiteness-not-inherited-by-quotients`, `stable-finiteness-failure-refutes-surjunctivity`.
* `gk-kdf-structure`: the same question from the kernel and structure side: the kernel of
  `F_2[R^x] -> R`, idempotents, K-theory, corner amplification inside `F_2[R^x]`, trace-like and
  augmentation invariants. Construct the lift or prove it impossible.
* `gk-invariant-output`: a nonlinear injective automaton over `R^x` whose output is constant on
  right cosets of a finite subgroup (`leavitt-units-carry-injective-invariant-output-automaton`,
  `invariant-output-injective-automata-need-invisible-symmetry`).
* `gk-defect-automaton`: Garden-of-Eden windows must fold on sofic-invisible elements
  (`sofic-radical-localizes-garden-of-eden-windows`). Design an automaton whose injectivity is
  certified by the exact compression relations of the nonsoficity configuration
  (`u L u^-1 <= L`, `c` in `C(L)`), with its window on the defect `[u c u^-1, l]`.
* `gk-design-group`: choose the group last. Find local rules `tau`, `sigma` and a finite partial
  product table where `sigma o tau = id` and `tau` has a Garden of Eden, then realize the table
  in a group while escaping every surjunctive marked cover
  (`forward-memory-lifts-exclude-strict-cellular-sections`,
  `certificate-controlled-routing-is-surjunctive`, `surjunctive-guard-subgroups-force-surjectivity`).
* `gk-other-hosts`: nonsofic hosts outside every proven permanence class: Fournier-Facio's
  torsion-free group, `EL_n` over d-ary Leavitt algebras, amalgams and non-split extensions of
  Kun–Thom pairs, Thompson's `V` and topological full groups. Counterexample or surjunctivity,
  host by host.

Positive side (prove every group surjunctive):
* `gk-rokhlin`: measure and entropy without finite models: push Bernoulli measure through an
  injective automaton; Seward-type maximal Rokhlin entropy of Bernoulli shifts as a sufficient
  condition (the criterion Bowen–Chapman use); entropy of the image subshift.
* `gk-three-factor`: prove or refute `three-factor-finite-alphabet-ca-are-surjunctive`, which by
  `stable-three-factor-reduction-proves-gottschalk` is the whole conjecture.
* `gk-fixed-host`: surjunctivity of the fixed tester `U`
  (`gottschalk-surjunctivity-fixed-two-generator-tester`,
  `universal-all-group-subgroup-colimit-class-tester`), starting from the host's construction
  and the landed permanence theorems. The peer lane `gottschalk-positive-host` works the same route.
* `gk-leavitt-positive`: prove `R^x` surjunctive by extending the finitary permanence method
  (`finitary-split-extension-surjunctivity-permanence`, graph folds, LEF lamps) to self-similar
  groups, ample groupoids and topological full groups; Thompson's `V` first.
* `gk-decoder-fiber`: route `gottschalk-via-countable-transitive-decoder-fiber`.
* `gk-observables`: route `gottschalk-via-matrix-observable-extension`, and operator-algebraic
  analogues of the characteristic-zero Kaplansky proof (traces on observable algebras).
* `gk-logic`: compactness and model theory: reduce the conjecture to its exact finitary
  combinatorial core (partial product tables, ultraproducts, marked covers), then prove the
  core or exhibit a table that some group realizes and no surjunctive cover does.
* `gk-free`: no assigned start. Survey the whole region and take the approach you judge most
  likely to decide the conjecture.

Verification and graph:
* `gk-verify-neg`: adversarially re-derive every negative-side claim from any lane or peer:
  certificates, injectivity proofs, Garden-of-Eden patterns, checker conventions, statement
  fidelity. Land corrections forward.
* `gk-verify-pos`: the same for positive-side claims: permanence theorems, reductions, route
  validity, and that nothing establishes the goal prematurely.
* `gk-cairn-steward`: keeps the region green and legible. Poll main about every 20 minutes for
  Gottschalk-region landings. Run `cairn check` on MSI in a `--shared` clone at the pushed tip
  (one core, one run at a time, at most one run per 30 minutes; recipe in
  `$SP/../829306b2-1fe5-42c3-a312-35bcc8c1425f/scratchpad/cairncheck.sh` and the memory
  cairn-node-authoring-gotchas). Fix wiring forward, message lanes about their errors, check
  `cairn why gottschalk-surjunctivity-conjecture` and `cairn why leavitt-unit-group-nonsurjunctive`
  after each batch, and keep the goal node's `## Attempts` current.
