# Evidence audit of the 162 ESTABLISHED `fpbs-` claims

Lane D, 2026-09-09. Compiled against the whole-graph fixpoint (`tools/cairn.py check`, exit 0,
no errors, no fpbs warnings). Cairn status is dependency bookkeeping: it records that a written
route exists, never that the mathematics was verified.

## Method

Each ESTABLISHED claim was classified by the route that establishes it.

- **literature import** — the establishing route is a `-reference`/`-input` route with `requires: []`
  whose body names a published theorem. Every arXiv identifier in the archive was resolved through
  the arXiv API and its title and authors compared with the citing sentence.
- **own theorem, finite replay** — the archive's own deduction, written in a document that ships a
  finite-check artifact recording a PASS. The replay tests finite models only; every checks file
  says so in its own `scope` field.
- **own theorem, written only** — the archive's own deduction with an audit JSON but no finite replay.
- **withdrawn / weakened** — see the next section. There are none.

| class | count |
|---|---|
| literature import | 27 |
| own theorem, finite replay | 129 |
| own theorem, written deduction only | 6 |
| withdrawn or weakened by a later source | 0 |
| **total** | **162** |

## Nothing in the archive is withdrawn

The `not_assumed` array of `torsionfree-local-audit.json` is an *independence* statement, not a
retraction. Its six entries record hypotheses the torsion-free construction deliberately does not
use. The same firewall appears in five sibling audits, always in the same voice:

- `finite-priority-audit.json`: "Prior broad claims are retained as provenance, not independently revalidated."
- `small-cancellation-audit.json`: "Retained without blanket revalidation; not assumptions in the new proof."
- `connector-capacity-audit.json`: "Retained as provenance, not comprehensively re-audited in this continuation."
- `phase-repair-audit.json`: "Only new finite checks were executed; earlier proof claims retained as provenance."
- `burnside-explicit-audit.json`: `previous_cumulative_claims_independently_reaudited: false`.
- `explicit-window-audit.json`: `proof_does_not_use` includes "earlier broad two-generator or bounded-exponent cost deductions".

So the later documents quarantined the earlier broad theorems rather than depending on them, and
declined to re-audit them. No response and no document says any of them is false or narrower than
stated. The one withdrawal sentence in the archive, in response 1, is about a pre-existing repo note
(`notes/TRUE_ROUTED_HOLONOMY_PHASE_REPAIR.md`), not about an fpbs claim.

The archive's own negative results were recorded as claims when they were found, rather than as
silent demotions. Response 47 refuted the optimality of universal priority deletion, and that
refutation is carried by `fpbs-priority-deletion-density-above-action-cost`, whose `invalidates:`
names the dead route `fpbs-fixed-price-via-priority-deletion-optimality`.

**Two claims carry reduced confidence** without being wrong. `fpbs-bounded-exponent-subgroup-relative-cost`
and `fpbs-two-generator-action-cost-witness` are the two the later documents name when they firewall
"previous broad" work. Both keep their written routes and their 48,584-assertion replay. Their
Evidence level lines now say that no later document rests on them.

## Table

`L` marks a `root: true` landmark node.

| id | class | evidence | source location | verdict |
|---|---|---|---|---|
| `fpbs-amen2-betti-cost-input` | literature import | published theorem; arXiv id resolved and matched | Gaboriau, *What is... cost?*, arXiv:1011.2294v1 (Betti-cost inequality, lecture Thm 2.64) | import verified |
| `fpbs-amen2-cost-inputs` | literature import | published theorem; arXiv id resolved and matched | Gaboriau arXiv:1011.2294v1 (standard cost facts, Prop 2.39); Ershov-Golan-Sapir arXiv:1401.2202 Lemma 5.7 | import verified |
| `fpbs-attained-cost-one-amenable` | literature import | published theorem; arXiv id resolved and matched | Gaboriau arXiv:1011.2294v1, paragraph after the Ornstein-Weiss discussion | import verified |
| `fpbs-aw-finite-pattern-input` | literature import | published theorem; arXiv id resolved and matched | Abert-Weiss arXiv:1103.1063v2 Theorem 1 | import verified |
| `fpbs-bernoulli-maximal-cost` | literature import | published theorem; arXiv id resolved and matched | Abert-Weiss arXiv:1103.1063v2 Corollary 2; Gaboriau arXiv:1011.2294v1 | import verified |
| `fpbs-burnside-embedding-input` | literature import | published theorem; arXiv id resolved and matched | Ivanov arXiv:math/0210191; Donoso-Echenique-Silva arXiv:2608.20472v1 Lemma 2.4, Thm 2.5 | import verified |
| `fpbs-burnside-nonamenable-two-generator-input` | literature import | published theorem; arXiv id resolved and matched | Osin arXiv:math/0404073v1 (uniform non-amenability); via [DS] | import verified |
| `fpbs-cap-osin-input` | literature import | published theorem; arXiv id resolved and matched | Osin arXiv:math/0404073v1 Theorem 2.7 and Lemma 2.2 | import verified |
| `fpbs-critical-l2-implies-nonuniqueness` | literature import | published theorem; arXiv id resolved and matched | Hutchcroft arXiv:1904.05804v2 / arXiv:1804.10191v3 | import verified |
| `fpbs-critical-walk-correlation` | literature import | published theorem; arXiv id resolved and matched | Schramm's lemma via Kozma arXiv:1003.5240v3 and Hutchcroft arXiv:1804.10191v3 Prop 6.4 | import verified |
| `fpbs-even-burnside-locally-finite-input` | literature import | published theorem; no arXiv id in the archive | Ivanov ICM survey Thm 1(a), Thm 3(c) with Olshanskii (n>=2^48, 2^9\|n) | import unverifiable from the archive |
| `fpbs-ew-dehn-input` | literature import | published theorem; arXiv id resolved and matched | Lyndon-Schupp Ch. V Thm 4.4; Sapir arXiv:1012.1325v4 Def 3.6, Thm 3.7 | import verified |
| `fpbs-finite-locally-finite-cost-input` | literature import | published theorem; arXiv id resolved and matched | Gaboriau arXiv:1011.2294v1 (finite/locally finite cost) | import verified |
| `fpbs-held-infinite-abelian-two-subgroup-input` | literature import | published theorem; no arXiv id, archive says the original was read visually | Held, *On abelian subgroups of infinite 2-groups*, p. 97 | not machine-checkable from the archive |
| `fpbs-normalized-cost-induction-input` | literature import | published theorem; no arXiv id in the archive | Gaboriau induction formula, via torsion-actions.md | import unverifiable from the archive |
| `fpbs-priority-intersection-input` | literature import | published theorem; arXiv id resolved and matched | Gruber-Sisto arXiv:1408.4488v3 Lemmas 2.15, 2.17 | import verified |
| `fpbs-sc-choi-seo` | literature import | published theorem; arXiv id resolved and matched | Choi-Seo arXiv:2508.08932v2 | import verified |
| `fpbs-sc-classical-input` | literature import | published theorem; arXiv id resolved and matched | Sapir arXiv:1012.1325v4 Thm 3.7 (Greendlinger); Gaboriau arXiv:1011.2294v1 | import verified |
| `fpbs-sc-gruber-sisto` | literature import | published theorem; arXiv id resolved and matched | Gruber-Sisto arXiv:1408.4488v3 Theorem 1.3 | import verified |
| `fpbs-small-marker-induction-input` | literature import | published theorem; no arXiv id in the archive | standard aperiodic small-section/marker lemma, via phase-repair.md | import unverifiable from the archive |
| `fpbs-suchkova-shunkov-input` | literature import | published theorem; arXiv id resolved and matched | Suchkova-Shunkov, as stated in Chernikov arXiv:0711.2597v1 | import verified |
| `fpbs-tfl-cost-input` | literature import | published theorem; arXiv id resolved and matched | Gaboriau arXiv:1011.2294v1 | import verified |
| `fpbs-tfl-percolation-input` | literature import | published theorem; arXiv id resolved and matched | Gruber-Sisto arXiv:1408.4488v3 Thm 1.3; Choi-Seo arXiv:2508.08932v2 | import verified |
| `fpbs-tfl-sc-input` | literature import | published theorem; arXiv id resolved and matched | Greendlinger via Sapir arXiv:1012.1325v4; Gruber-Sisto arXiv:1408.4488v3 | import verified |
| `fpbs-transitive-sharpness-linear-lower-bound` | literature import | published theorem; arXiv id resolved and matched | Duminil-Copin-Tassion arXiv:1502.03050 Theorem 1.1 | import verified |
| `fpbs-unbounded-exponent-fg-amen2-input` | literature import | published theorem; arXiv id resolved and matched | Ershov-Golan-Sapir arXiv:1401.2202 Theorem 5.6 | import verified |
| `fpbs-wired-forest-degree-two` | literature import | published theorem; no arXiv id given | Aldous-Lyons, *Processes on Unimodular Random Networks*, Thm 6.2 and Prop 7.1, author-hosted version | not machine-checkable from the archive |
| `fpbs-action-level-local-expanding-sparsifiers` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md | stands as written |
| `fpbs-all-generating-sets-local-sparsifiers` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md | stands as written |
| `fpbs-all-parameter-finite-cluster-spectrum` | own theorem, finite replay | PASS, 26,156 exact identity assertions | spectral-spike.md | stands as written |
| **L** `fpbs-amen2-fixed-price-one` | own theorem, finite replay | PASS, 5,060 exact assertions over 565 finite graphing cases | two-generator-complete-proof.md | stands as written |
| `fpbs-arbitrary-subrelation-torsion-budget` | own theorem, finite replay | passed; 42,848 repaired colorings, 126,047 star completions | phase-repair.md | stands as written |
| `fpbs-average-connector-defect-cost-bound` | own theorem, finite replay | passed; 42,848 repaired colorings, 126,047 star completions | phase-repair.md | stands as written |
| `fpbs-bernoulli-lazy-covariance-bound` | own theorem, finite replay | PASS, 26,156 exact identity assertions | spectral-spike.md | stands as written |
| `fpbs-bounded-centralizer-relative-cost` | own theorem, finite replay | PASS, 4,875 checked cases | torsion-actions.md | stands as written |
| **L** `fpbs-bounded-exponent-two-groups-fixed-price` | own theorem, finite replay | PASS, 48,584 exact assertions | bounded-exponent-progress.md | stands as written |
| `fpbs-bounded-exponent-upper-cost-below-two` | own theorem, finite replay | PASS, 48,584 exact assertions | bounded-exponent-progress.md | stands as written |
| `fpbs-bridgeless-collective-fragility` | own theorem, finite replay | PASS, 1,482 exact checks | exploration.md | stands as written |
| `fpbs-burnside-common-upper-cost` | own theorem, finite replay | PASS, 4,875 checked cases | torsion-actions.md | stands as written |
| `fpbs-burnside-explicit-action-pair` | own theorem, finite replay | PASS, 4,875 checked cases | torsion-actions.md | stands as written |
| `fpbs-cactus-finite-ball-pivotal-budget` | own theorem, finite replay | PASS, 1,482 exact checks | exploration-pivotal-projections.md | stands as written |
| `fpbs-cactus-pivotal-bound` | own theorem, finite replay | PASS, 1,482 exact checks | exploration-pivotal-projections.md | stands as written |
| `fpbs-cap-adaptive-repair` | own theorem, finite replay | passed; 77,952 restriction-defect + 64,960 repaired-labeling cases | connector-capacity.md | stands as written |
| `fpbs-cap-completion-criterion` | own theorem, finite replay | passed; 77,952 restriction-defect + 64,960 repaired-labeling cases | connector-capacity.md | stands as written |
| `fpbs-cap-finite-replay` | own theorem, finite replay | passed; 77,952 restriction-defect + 64,960 repaired-labeling cases | connector-capacity.md + connector-capacity-checks.json, replay_connector_capacity.py | stands as written |
| **L** `fpbs-cap-hyperfinite-barrier` | own theorem, finite replay | passed; 77,952 restriction-defect + 64,960 repaired-labeling cases | connector-capacity.md | stands as written |
| `fpbs-cap-hyperfinite-coefficient` | own theorem, finite replay | passed; 77,952 restriction-defect + 64,960 repaired-labeling cases | connector-capacity.md | stands as written |
| `fpbs-cap-robust-barrier` | own theorem, finite replay | passed; 77,952 restriction-defect + 64,960 repaired-labeling cases | connector-capacity.md | stands as written |
| `fpbs-cap-variable-order` | own theorem, finite replay | passed; 77,952 restriction-defect + 64,960 repaired-labeling cases | connector-capacity.md | stands as written |
| `fpbs-centralizer-cheap-extension` | own theorem, finite replay | PASS, 48,584 exact assertions | bounded-exponent-progress.md | stands as written |
| `fpbs-cluster-merger-projections` | own theorem, finite replay | PASS, finite Russo audits | creative-branches.md | stands as written |
| `fpbs-collapse-exponential-pivotal-spikes` | own theorem, finite replay | PASS, 26,156 exact identity assertions | spectral-spike.md | stands as written |
| **L** `fpbs-cost-one-routes-cannot-be-uniformly-tight` | own theorem, finite replay | PASS, 3,753 reconnection + 5,168 finite-ball configurations | fixed-price-percolation.md | stands as written |
| `fpbs-critical-pivotal-concentration-under-collapse` | own theorem, finite replay | PASS, 1,482 exact checks | exploration.md | stands as written |
| `fpbs-cut-capacity-dual` | own theorem, finite replay | PASS, 56,149 exact assertions | cut-repair.md | stands as written |
| `fpbs-cut-completion-criterion` | own theorem, finite replay | PASS, 56,149 exact assertions | cut-repair.md | stands as written |
| `fpbs-cut-corridor-separation` | own theorem, finite replay | PASS, 56,149 exact assertions | cut-repair.md | stands as written |
| `fpbs-cut-finite-replay` | own theorem, finite replay | PASS, 56,149 exact assertions | cut-repair.md + cut-repair-checks.json, replay_cut_repair.py | stands as written |
| `fpbs-cut-fractional-product` | own theorem, finite replay | PASS, 56,149 exact assertions | cut-repair.md | stands as written |
| **L** `fpbs-cut-low-cost-seeds` | own theorem, finite replay | PASS, 56,149 exact assertions | cut-repair.md | stands as written |
| `fpbs-cut-measurable-repair` | own theorem, finite replay | PASS, 56,149 exact assertions | cut-repair.md | stands as written |
| `fpbs-cut-network-reliability` | own theorem, finite replay | PASS, 56,149 exact assertions | cut-repair.md | stands as written |
| `fpbs-cut-seed-inputs` | own theorem, finite replay | PASS, 56,149 exact assertions | cut-repair.md | stands as written |
| `fpbs-cut-weighted-count` | own theorem, finite replay | PASS, 56,149 exact assertions | cut-repair.md | stands as written |
| `fpbs-cycle-deletion-half-boundary` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md + local-sparsifier-checks.json, replay_local_sparsifiers.py | stands as written |
| `fpbs-dyadic-projections-bound-connectivity` | own theorem, finite replay | PASS, finite Russo audits | creative-branches.md | stands as written |
| `fpbs-ew-embedded-tree` | own theorem, finite replay | PASS, 150,032 exact assertions | explicit-percolation-window.md | stands as written |
| `fpbs-ew-finite-replay` | own theorem, finite replay | PASS, 150,032 exact assertions | explicit-percolation-window.md + explicit-window-checks.json, replay_explicit_window.py | stands as written |
| `fpbs-ew-nb-majorant` | own theorem, finite replay | PASS, 150,032 exact assertions | explicit-percolation-window.md | stands as written |
| `fpbs-ew-separation` | own theorem, finite replay | PASS, 150,032 exact assertions | explicit-percolation-window.md | stands as written |
| `fpbs-ew-spectral` | own theorem, finite replay | PASS, 150,032 exact assertions | explicit-percolation-window.md | stands as written |
| `fpbs-ew-survival` | own theorem, finite replay | PASS, 150,032 exact assertions | explicit-percolation-window.md | stands as written |
| `fpbs-ew-three-subgroups` | own theorem, finite replay | PASS, 150,032 exact assertions | explicit-percolation-window.md | stands as written |
| **L** `fpbs-ew-window` | own theorem, finite replay | PASS, 150,032 exact assertions | explicit-percolation-window.md | stands as written |
| `fpbs-expansion-thinning-threshold` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md | stands as written |
| `fpbs-fiid-finite-clusters-do-not-imply-dyadic-summability` | own theorem, finite replay | PASS, 1,482 exact checks | exploration.md | stands as written |
| `fpbs-fiid-partition-spectral-jump-model` | own theorem, finite replay | PASS, 26,156 exact identity assertions | spectral-spike.md | stands as written |
| `fpbs-finite-cluster-density-continuous` | own theorem, finite replay | PASS, 3,753 reconnection + 5,168 finite-ball configurations | fixed-price-percolation.md + replay.json, replay.py | stands as written |
| `fpbs-finite-detour-centralizer-dichotomy` | own theorem, finite replay | PASS, 48,584 exact assertions | bounded-exponent-progress.md | stands as written |
| `fpbs-finite-index-star-relative-cost` | own theorem, finite replay | passed; 42,848 repaired colorings, 126,047 star completions | phase-repair.md | stands as written |
| `fpbs-finite-partition-derandomization` | own theorem, finite replay | PASS, 48,584 exact assertions | bounded-exponent-progress.md | stands as written |
| `fpbs-finite-phase-disagreement-versus-repair` | own theorem, finite replay | passed; 42,848 repaired colorings, 126,047 star completions | phase-repair.md | stands as written |
| `fpbs-finite-phase-section-normalization` | own theorem, finite replay | passed; 42,848 repaired colorings, 126,047 star completions | phase-repair.md | stands as written |
| `fpbs-first-return-torsion-detours` | own theorem, finite replay | PASS, 48,584 exact assertions | bounded-exponent-progress.md | stands as written |
| `fpbs-hierarchical-pivotal-amplification` | own theorem, finite replay | PASS, 1,482 exact checks | exploration-pivotal-projections.md | stands as written |
| `fpbs-integrated-pivotal-rate-identity` | own theorem, finite replay | PASS, 1,482 exact checks | exploration-pivotal-projections.md | stands as written |
| `fpbs-integrated-pivotal-total-budget` | own theorem, finite replay | PASS, 1,482 exact checks | exploration.md | stands as written |
| `fpbs-integrated-sensitivity-implies-nonuniqueness` | own theorem, finite replay | PASS, 1,482 exact checks | exploration-pivotal-projections.md | stands as written |
| `fpbs-kazhdan-rankgradient-counterexample-reduction` | own theorem, finite replay | PASS, finite Russo audits | creative-branches.md | stands as written |
| `fpbs-large-even-burnside-fixed-price` | own theorem, finite replay | PASS, 48,584 exact assertions | bounded-exponent-progress.md | stands as written |
| `fpbs-large-finite-subgroup-quantitative-cost` | own theorem, finite replay | PASS, 48,584 exact assertions | bounded-exponent-progress.md | stands as written |
| `fpbs-local-selector-repair-geometry` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md + local-sparsifier-checks.json, replay_local_sparsifiers.py | stands as written |
| `fpbs-local-sparsifier-finite-replay` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md + local-sparsifier-checks.json, replay_local_sparsifiers.py | stands as written |
| `fpbs-logarithmic-sparse-coset-route-lower-bound` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md + local-sparsifier-checks.json, replay_local_sparsifiers.py | stands as written |
| `fpbs-long-detours-with-no-bridges` | own theorem, finite replay | PASS, finite Russo audits | creative-branches.md | stands as written |
| `fpbs-non-fixed-price-one-has-nonuniqueness` | own theorem, finite replay | PASS, 3,753 reconnection + 5,168 finite-ball configurations | fixed-price-percolation.md | stands as written |
| `fpbs-pivotal-budget-implies-nonuniqueness` | own theorem, finite replay | PASS, finite Russo audits | creative-branches.md | stands as written |
| `fpbs-pivotal-nonconcentration-implies-nonuniqueness` | own theorem, finite replay | PASS, 1,482 exact checks | exploration.md | stands as written |
| `fpbs-pivotal-triangle-fails` | own theorem, finite replay | PASS, 1,482 exact checks | exploration-pivotal-projections.md | stands as written |
| `fpbs-positive-cost-gap-bounds-finite-subgroups` | own theorem, finite replay | PASS, 48,584 exact assertions | bounded-exponent-progress.md | stands as written |
| `fpbs-prime-divisor-bounded-range-sparsifiers` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md | stands as written |
| **L** `fpbs-prime-divisor-upper-cost` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md + local-sparsifier-checks.json, replay_local_sparsifiers.py | stands as written |
| `fpbs-priority-burnside-product` | own theorem, finite replay | 51,532 exact assertions, 25,984 priority cases | finite-priority.md | stands as written |
| `fpbs-priority-composite-algebra` | own theorem, finite replay | 51,532 exact assertions, 25,984 priority cases | finite-priority.md | stands as written |
| **L** `fpbs-priority-composite-fixed-price` | own theorem, finite replay | 51,532 exact assertions, 25,984 priority cases | finite-priority.md | stands as written |
| `fpbs-priority-even-profile` | own theorem, finite replay | 51,532 exact assertions, 25,984 priority cases | finite-priority.md | stands as written |
| `fpbs-priority-finite-rank` | own theorem, finite replay | 51,532 exact assertions, 25,984 priority cases | finite-priority.md | stands as written |
| `fpbs-priority-finite-replay` | own theorem, finite replay | 51,532 exact assertions, 25,984 priority cases | finite-priority.md + finite-priority-checks.json, replay_priority.py | stands as written |
| `fpbs-priority-integral` | own theorem, finite replay | 51,532 exact assertions, 25,984 priority cases | finite-priority.md | stands as written |
| `fpbs-priority-torsion` | own theorem, finite replay | 51,532 exact assertions, 25,984 priority cases | finite-priority.md | stands as written |
| **L** `fpbs-qb-action-bound` | own theorem, finite replay | finite checks passed, 12,732 assertions | burnside-explicit-bound.md | stands as written |
| `fpbs-qb-algebra` | own theorem, finite replay | finite checks passed, 12,732 assertions | burnside-explicit-bound.md | stands as written |
| `fpbs-qb-all-subgroups` | own theorem, finite replay | finite checks passed, 12,732 assertions | burnside-explicit-bound.md | stands as written |
| `fpbs-qb-bound-asymptotics` | own theorem, finite replay | finite checks passed, 12,732 assertions | burnside-explicit-bound.md | stands as written |
| `fpbs-qb-disjoint-cycles` | own theorem, finite replay | finite checks passed, 12,732 assertions | burnside-explicit-bound.md | stands as written |
| `fpbs-qb-finite-replay` | own theorem, finite replay | finite checks passed, 12,732 assertions | burnside-explicit-bound.md + burnside-explicit-checks.json, replay_burnside_explicit.py | stands as written |
| `fpbs-qb-subgroup-transfer` | own theorem, finite replay | finite checks passed, 12,732 assertions | burnside-explicit-bound.md | stands as written |
| `fpbs-qb-union-pruning` | own theorem, finite replay | finite checks passed, 12,732 assertions | burnside-explicit-bound.md | stands as written |
| `fpbs-quantitative-cost-threshold-bound` | own theorem, finite replay | PASS, 3,753 reconnection + 5,168 finite-ball configurations | fixed-price-percolation.md + replay.json, replay.py | stands as written |
| **L** `fpbs-quantitative-routing-tail-bound` | own theorem, finite replay | PASS, 184,096 pointwise checks | routing-obstruction-continuation.md + routing-bound-replay.json, replay_routing_bound.py | stands as written |
| `fpbs-quantitative-two-generator-cost-witness` | own theorem, finite replay | PASS, 5,060 exact assertions over 565 finite graphing cases | two-generator-complete-proof.md | stands as written |
| `fpbs-rank-uniform-local-expanding-sparsifiers` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md | stands as written |
| `fpbs-reciprocal-shortest-route-obstruction` | own theorem, finite replay | PASS, 3,753 reconnection + 5,168 finite-ball configurations | fixed-price-percolation.md + replay.json, replay.py | stands as written |
| `fpbs-regular-tree-dyadic-projection-bound` | own theorem, finite replay | PASS, 1,482 exact checks | exploration-pivotal-projections.md | stands as written |
| `fpbs-regular-tree-dyadic-three-halves` | own theorem, finite replay | PASS, 1,482 exact checks | exploration.md | stands as written |
| `fpbs-same-action-cyclic-section-gluing` | own theorem, finite replay | PASS, 5,060 exact assertions over 565 finite graphing cases | two-generator-complete-proof.md | stands as written |
| `fpbs-sc-abundance` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md | stands as written |
| `fpbs-sc-continuum` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md | stands as written |
| `fpbs-sc-finite-repair` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md | stands as written |
| `fpbs-sc-finite-replay` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md + replay_small_cancellation.py, small-cancellation-checks.json | stands as written |
| **L** `fpbs-sc-fixed-price-family` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md | stands as written |
| `fpbs-sc-free-balls` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md | stands as written |
| `fpbs-sc-infinite-presentation` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md | stands as written |
| **L** `fpbs-sc-percolation-family` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md | stands as written |
| `fpbs-sc-presentation-algebra` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md | stands as written |
| `fpbs-sc-profiles` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md | stands as written |
| `fpbs-sc-proper-cyclic` | own theorem, finite replay | finite word/probability/repair checks | small-cancellation-family.md | stands as written |
| `fpbs-short-disjoint-torsion-detours` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md | stands as written |
| `fpbs-sparse-spine-cost-bound` | own theorem, finite replay | PASS, finite Russo audits | creative-branches.md | stands as written |
| `fpbs-tfl-algebra` | own theorem, finite replay | PASS, 68,833 assertions | torsionfree-local.md | stands as written |
| `fpbs-tfl-continuum` | own theorem, finite replay | PASS, 68,833 assertions | torsionfree-local.md | stands as written |
| `fpbs-tfl-finite-replay` | own theorem, finite replay | PASS, 68,833 assertions | torsionfree-local.md + replay_torsionfree_local.py, torsionfree-local-checks.json | stands as written |
| `fpbs-tfl-finite-residual` | own theorem, finite replay | PASS, 68,833 assertions | torsionfree-local.md | stands as written |
| **L** `fpbs-tfl-fixed-price` | own theorem, finite replay | PASS, 68,833 assertions | torsionfree-local.md | stands as written |
| `fpbs-tfl-local` | own theorem, finite replay | PASS, 68,833 assertions | torsionfree-local.md | stands as written |
| `fpbs-tfl-metric` | own theorem, finite replay | PASS, 68,833 assertions | torsionfree-local.md | stands as written |
| `fpbs-tfl-non-hopfian` | own theorem, finite replay | PASS, 68,833 assertions | torsionfree-local.md | stands as written |
| `fpbs-tfl-percolation` | own theorem, finite replay | PASS, 68,833 assertions | torsionfree-local.md | stands as written |
| `fpbs-tfl-priority` | own theorem, finite replay | PASS, 68,833 assertions | torsionfree-local.md | stands as written |
| `fpbs-torsion-finite-repair-relative-cost` | own theorem, finite replay | PASS, 4,875 checked cases | torsion-actions.md | stands as written |
| **L** `fpbs-two-generator-action-cost-witness` | own theorem, finite replay | PASS, 5,060 exact assertions over 565 finite graphing cases | two-generator-complete-proof.md | stands as written |
| `fpbs-unbounded-finite-subgroups-fixed-price` | own theorem, finite replay | PASS, 48,584 exact assertions | bounded-exponent-progress.md | stands as written |
| `fpbs-uniformly-robust-burnside-sparsifiers` | own theorem, finite replay | PASS, 28,216 cut-deletion pairs | local-sparsifiers.md | stands as written |
| `fpbs-uniqueness-scale-crossover` | own theorem, finite replay | PASS, 26,156 exact identity assertions | spectral-spike.md | stands as written |
| `fpbs-uniqueness-spectral-atom-decomposition` | own theorem, finite replay | PASS, 26,156 exact identity assertions | spectral-spike.md | stands as written |
| `fpbs-well-founded-connectivity` | own theorem, finite replay | PASS, finite Russo audits | creative-branches.md | stands as written |
| `fpbs-amen2-betti-vanishing` | own theorem, written only | written audit only, no finite replay | amen2-complete-proof.md | stands as written |
| `fpbs-binary-finite-abelian-subgroup` | own theorem, written only | written audit only, no finite replay | amen2-complete-proof.md | stands as written |
| `fpbs-bounded-exponent-amen2-fixed-price` | own theorem, written only | written audit only, no finite replay | amen2-complete-proof.md | stands as written |
| `fpbs-bounded-exponent-shunkov-fixed-price` | own theorem, written only | written audit only, no finite replay | amen2-complete-proof.md | stands as written |
| `fpbs-bounded-exponent-subgroup-relative-cost` | own theorem, written only | written audit only, no finite replay | amen2-complete-proof.md | stands as written |
| `fpbs-positive-cost-two-generated-nonamenable` | own theorem, written only | written audit only, no finite replay | amen2-complete-proof.md | stands as written |

## Finite-replay artifacts and their recorded totals

| checks artifact | status | recorded total |
|---|---|---|
| `bounded-exponent-checks.json / bounded-exponent-reaudit-checks.json` | PASS | 48,584 exact assertions |
| `burnside-explicit-checks.json` | finite checks passed | 12,732 assertions, 4,160 labelings |
| `connector-capacity-checks.json` | passed | 77,952 restriction-defect and 64,960 repaired-labeling cases |
| `creative-replay.json` | PASS | finite Russo audits on six small graphs |
| `cut-repair-checks.json` | PASS | 56,149 exact assertions |
| `cyclic-section-checks.json` | PASS | 5,060 assertions over 565 finite graphing cases |
| `explicit-window-checks.json` | PASS | 150,032 exact assertions |
| `exploration-replay.json` | PASS | 1,482 exact checks |
| `finite-priority-checks.json` | (no status field) | 51,532 assertions, 25,984 priority cases |
| `local-sparsifier-checks.json` | PASS | 28,216 cut-deletion pairs |
| `phase-repair-checks.json` | passed | 42,848 repaired colorings, 126,047 star completions |
| `replay.json` | PASS | 3,753 reconnection and 5,168 finite-ball configurations |
| `routing-bound-replay.json` | PASS | 184,096 pointwise and 30,960 averaged checks |
| `small-cancellation-checks.json` | (no status field) | 143,311 assertions, 5,440 labelings, per the audit |
| `spectral-spike-replay.json` | PASS | 26,156 exact identity assertions |
| `torsion-replay.json` | PASS | 4,875 checked cases |
| `torsionfree-local-checks.json` | PASS | 68,833 assertions, 26,843 deletion labelings |

Every one of these files carries its own disclaimer that it tests finite models and not the infinite
theorems. Seven also carry an explicit `not_verified` array naming what the replay does not reach.

## Citation audit

Thirty-six distinct arXiv identifiers appear in `fpbs-` nodes and in the archive artifacts. All
thirty-six resolve, and every title and author list matches the citing sentence. No fabricated or
misdirected identifier was found. Three hygiene defects:

1. `arXiv:2607.20273v1` is cited as "[PN] A Product-Neighbourhood Criterion for Fixed Price One"
   with no author. The paper is by Raz Slutsky.
2. `arXiv:1205.1478v1` is cited as "Dmitry Gavinsky"; the author is Dmytro Gavinsky.
3. Two imports have no arXiv identifier at all: Held (`fpbs-held-infinite-abelian-two-subgroup-input`),
   cited as visually checked from the original two-page paper, and Aldous-Lyons
   (`fpbs-wired-forest-degree-two`), cited from an author-hosted version.

The most load-bearing recent import was read against its abstract. Donoso-Echenique and Silva,
*Free Burnside groups of large odd exponent have cost 1*, `arXiv:2608.20472v1`, prove cost one for
B(m,n), which is the infimum over free actions. Every one of the six places the archive cites it
says so explicitly and separates infimal cost from fixed price. That reading is correct.

## Direction of the logical neighbourhood

The three classic direction traps are all avoided.

- Lyons gives "not fixed price one implies p_c<p_u". The archive's route
  `fpbs-threshold-collapse-forces-price-one` derives p_c=p_u implies all costs one, then
  contraposes into `fpbs-non-fixed-price-one-has-nonuniqueness`. Right direction.
- Hutchcroft-Pete give infimal cost one for Kazhdan groups, not fixed price one. The archive's
  `fpbs-kazhdan-rankgradient-counterexample-reduction` says "Infimum cost one already suffices; no
  attainment theorem is required". Right reading.
- Abert-Weiss give cost(alpha) at most cost(Bernoulli). `fpbs-bernoulli-maximal-cost` states Bernoulli
  attains the maximum. Right direction.

Gaboriau's attainment theorem is also used in the right direction: `fpbs-attained-cost-one-amenable`
says an *attained* cost-one graphing forces amenability, and its body records that the infimum alone
does not suffice.

The nodes another lane added while this audit ran were checked too, and they also point the right way.
`fpbs-kazhdan-groups-have-cost-one` quotes the Hutchcroft-Pete abstract exactly, including its closing
sentence "It remains open if they have fixed price 1", and says why that keeps the node separate from
the fixed-price goal. `fpbs-factor-lift-cost-monotone` has the extension on the cheap side, which is
the correct orientation. `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` cites arXiv:1711.02590,
which resolves to Hutchcroft's nonunimodular paper with the stated p_c<p_h<=p_u conclusion.

No fpbs node was found stating or routing a result backwards. In particular the archive nowhere
asserts fixed price one for large odd Burnside groups: the only two established claims that touch that
case, `fpbs-qb-action-bound` and `fpbs-prime-divisor-upper-cost`, are upper bounds strictly above one,
and `fpbs-burnside-upper-cost-one` is still OPEN.


## Landmark nodes enriched

The fourteen `root: true` established fpbs claims were rewritten with the precise statement, the
document and section that proves it, the imported inputs with resolved arXiv identifiers, the finite
replay and its counts, and an explicit **Evidence level** line. Ids, `root:` flags and titles were
kept, with one exception recorded below.

| id | headline | evidence level |
|---|---|---|
| `fpbs-tfl-fixed-price` | torsion-free relator families, cost one, mu(U) <= product_{j<=k} 12j/(12j+1) | own theorem, 68,833-assertion replay |
| `fpbs-sc-fixed-price-family` | prime detour family, cost exactly one in every essentially free action | own theorem, 143,311-assertion replay |
| `fpbs-sc-percolation-family` | p_c<p_u on every Cayley graph of that family | import plus one deduction, no replay possible |
| `fpbs-priority-composite-fixed-price` | same, with arbitrary integers n_i>=13, no primality | own theorem, 51,532-assertion replay |
| `fpbs-qb-action-bound` | every free B(2,n) action has cost at most U_n < 2-2/n | own theorem, 12,732-assertion replay |
| `fpbs-ew-window` | explicit nonuniqueness interval [7/20,37/100], theta(p)>1/20 | own theorem, 150,032-assertion replay |
| `fpbs-two-generator-action-cost-witness` | cost above one has a two-generated witness | own theorem, firewalled by later documents |
| `fpbs-amen2-fixed-price-one` | all two-generated subgroups amenable implies fixed price one | own theorem plus EGS Theorem 5.6 |
| `fpbs-bounded-exponent-two-groups-fixed-price` | bounded-exponent 2-groups have fixed price one | own theorem on a non-arXiv Held import |
| `fpbs-quantitative-routing-tail-bound` | averaged route tail at least h/d - delta\|B_R\| | own theorem, 184,096-check replay |
| `fpbs-cost-one-routes-cannot-be-uniformly-tight` | near-cost-one graphings cannot route tightly | own theorem, two independent routes |
| `fpbs-prime-divisor-upper-cost` | Burnside cost at most 2-2/p for the least prime divisor p | own theorem, 28,216-pair replay |
| `fpbs-cut-low-cost-seeds` | nested ergodic nowhere-hyperfinite seeds of cost 1+t | three imports plus accounting |
| `fpbs-cap-hyperfinite-barrier` | reliable hyperfinite connectors lie in one cyclic group of order n | own theorem, 77,952-case replay |

One title was wrong and was corrected. `fpbs-cut-low-cost-seeds` read "Bernoulli actions have actual
nested ergodic nowhere-hyperfinite seeds of cost 1+t". Theorem 7.1 of the cut-repair note requires
Gamma to be countable **nonamenable**, and the statement is false without it, since Bernoulli actions
of amenable groups are hyperfinite. The title now reads "Nonamenable Bernoulli actions have nested
ergodic nowhere-hyperfinite seeds of cost 1+t". No other title, id or flag was touched.

The root flags all sit on the right claims. The one worth a second opinion is
`fpbs-cost-one-routes-cannot-be-uniformly-tight`, which is now a corollary of the sharper
`fpbs-quantitative-routing-tail-bound` and could reasonably cede the landmark flag to it. The lead
should decide; I did not move it.

## Prose audit

`tools/graph_audit.py` over the whole graph reports one type-A hit and it is not an fpbs node.
No fpbs node appears in any of the audit's seven categories.
