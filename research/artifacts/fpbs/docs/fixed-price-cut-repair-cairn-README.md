# Fixed Price / Benjamini–Schramm: Cairn research addition

Neither universal problem is solved in this bundle. It contains a written
finite-cluster-corrected cost–threshold bound, an explicit reciprocal routing
obstruction, a compactness obstruction, and honest open dependency nodes.
No mathematical novelty or Lean formalization is claimed.

Read `research/artifacts/fixed-price-percolation.md` for the complete arguments,
scope, published prerequisites, and the exact remaining gaps.

## Replay

From this directory, with Python 3.10 or newer:

```sh
python3 scripts/replay.py --output research/artifacts/replay.json
./bin/cairn check --json
./bin/cairn why fpbs-benjamini-schramm-universal --json
./bin/cairn why fpbs-fixed-price-universal --json
```

The first command checks finite combinatorics and rational identities only.
Cairn checks the dependency graph, not mathematical proof validity. The two
universal targets and the fixed-price-one percolation kernel remain OPEN.

## Integration into the supplied project

The `research/fpbs-*.md` nodes and `research/artifacts/` material are an additive
research delta. Their `scripts/replay.py` dependency must also be retained.
The original research files are not modified. This isolated package includes
a byte-identical copy of the supplied Cairn implementation and its required
math display assets, a small launcher, and the supplied Apache-2.0 license. The copied source notes under
`source_excerpts/` are evidence for the archive audit, not new proof nodes.

The whole uploaded project had pre-existing compilation errors, including
unavailable git-pinned artifacts in a ZIP snapshot. Its saved baseline check
is not a successful verification. Isolated validation of these additions is
reported separately in `research/artifacts/cairn-check.json`.

## Attribution

The qualitative no-nonuniqueness => fixed-price-one implication is Lyons's
known theorem, using Abert–Weiss. Standard cost facts are imported from
Gaboriau. See the proof note's references. Do not relabel these results as a
new solution to either universal problem.

## Continuation

`research/artifacts/routing-obstruction-continuation.md` adds a quantitative
Cheeger-versus-routing tail inequality and records the unclosed operator
route. The two universal goals remain OPEN. To replay the new finite
inequalities (requires `networkx`):

```sh
python3 scripts/replay_routing_bound.py --output research/artifacts/routing-bound-replay.json
```

The new tests are not a proof of the infinite statements or of either conjecture.

## Creative branches

Read `research/artifacts/creative-branches.md`. The new universal pivotal and
dyadic estimates are OPEN, as are the sparse-spine and rank-gradient construction
targets. The known reductions and elementary identities are distinguished from
those hypotheses. The universal Fixed Price and Benjamini-Schramm goals remain
OPEN. This is not a formal proof package. Replay finite identities with:

```sh
python3 scripts/replay_creative.py --output research/artifacts/creative-replay.json
./bin/cairn check --json
```

## Exploration: exact tree benchmark and sharper pivotal target

Read `research/artifacts/exploration.md`. New proved statements distinguish
collective thinning from single-edge pivots, identify an integrated sensitivity
criterion, prove N^(-3/2) dyadic projection norms on regular trees, and construct
a dependent FIID counterexample to a weakened projection assertion.
The universal non-concentration and Bernoulli projection estimates remain OPEN.

```sh
python3 scripts/replay_exploration.py --output research/artifacts/exploration-replay.json
./bin/cairn check --json
```

The standard-library replay performs exact finite algebra checks and evaluates
explicit finite sums numerically. It is not a theorem prover. Prior artifacts
are retained as provenance and have not all been independently re-audited in
this continuation.


## Spectral-spike continuation (September 8, 2026)

Read `research/artifacts/spectral-spike.md` for the finite-cluster spectral
bound, exact uniqueness decomposition, exponentially high pivotal spikes
required under a collapsed window, and a non-percolation FIID partition
model with a matching abstract peak exponent. Neither universal goal is
solved; the decisive universal pivotal-rate upper estimate is OPEN.

```sh
python3 scripts/replay_spectral_spike.py
python3 tools/cairn.py check --json
python3 tools/cairn.py why fpbs-benjamini-schramm-universal --json
python3 tools/cairn.py why fpbs-fixed-price-universal --json
```

The replay checks exact finite identities, not infinite proofs. New proof
routes record written arguments and identified published inputs; Cairn's
ESTABLISHED status is dependency bookkeeping, not independent mathematical
verification. Prior material is retained as provenance.


## Action-level torsion continuation (September 8, 2026)

Read `research/artifacts/torsion-actions.md`. The finite-pattern paid-repair
argument works in the original free action. In sufficiently large odd free
Burnside groups it yields a common upper cost c_n across all infinite subgroups.
Two explicit actions have costs c_n and 1+(c_n-1)/n, but c_n=1 versus c_n>1
remains OPEN. This is not a verified counterexample or a universal solution.

```sh
python3 scripts/replay_torsion.py
python3 tools/cairn.py check --json
python3 tools/cairn.py why fpbs-fixed-price-universal --json
python3 tools/cairn.py why fpbs-benjamini-schramm-universal --json
```

The exact replay checks finite algebra, not infinite theorems. Cairn's
ESTABLISHED label records a supplied proof route, not external theorem
verification. Prior artifacts are retained as provenance and have not all
been re-audited. Both universal goals remain OPEN.


## Bounded-exponent progress (September 8, 2026)

Read `research/artifacts/bounded-exponent-progress.md`. The written argument
removes centralizer size and commutativity assumptions, gives zero relative cost
above every infinite subgroup in a bounded-exponent group, and proves a
quantitative fixed-price-one criterion from arbitrarily large finite subgroups.
Applications include all infinite bounded-exponent 2-groups (using Held) and the
explicit large even Burnside range (using Ivanov–Olshanskii). No novelty claim,
external referee certification, or formal verification is asserted.

```sh
python3 scripts/replay_bounded_exponent.py
python3 tools/cairn.py check --json
python3 tools/cairn.py why fpbs-bounded-exponent-two-groups-fixed-price --json
python3 tools/cairn.py why fpbs-fixed-price-universal --json
python3 tools/cairn.py why fpbs-benjamini-schramm-universal --json
```

The original universal goals remain OPEN. In particular, the odd-exponent
Burnside constant from the preceding note is not determined. Earlier artifacts
remain provenance rather than independently re-audited proof claims.


## Complete Amen_2 class proof (September 8, 2026)

Read `research/artifacts/amen2-complete-proof.md`. This continuation reproves the
bounded-exponent subgroup theorem and combines it with Suchkova-Shunkov to close
the bounded-exponent Amen_2 case. With the published Ershov-Golan-Sapir
unbounded-exponent theorem and a relative-cost exhaustion, all countably infinite
groups whose two-generated subgroups are amenable have fixed price one.
The first L2 Betti number consequently vanishes. No novelty, independent referee
approval, or formal theorem-verification claim is made.

The existing bounded-exponent finite replay was re-run: 48,584 exact assertions
and 5,952 exhaustive finite colorings passed. The newly imported algebraic
theorem is not computationally verified. The universal goals remain OPEN.

```sh
python3 scripts/replay_bounded_exponent.py --output research/artifacts/bounded-exponent-reaudit-checks.json
python3 tools/cairn.py check --json
python3 tools/cairn.py why fpbs-amen2-fixed-price-one --json
python3 tools/cairn.py why fpbs-fixed-price-universal --json
python3 tools/cairn.py why fpbs-benjamini-schramm-universal --json
```

Prior artifacts remain provenance rather than a claim of a complete independent
audit of every historical assertion in this cumulative bundle.


## Stronger action-wise witness theorem

The final standalone note is `research/artifacts/two-generator-complete-proof.md`.
It proves the stronger statement for a specified free action: cost greater than
one forces a two-generated subgroup restriction of cost greater than one.
The proof adds a same-action cyclic-compression identity and avoids an amenability
assumption on the pair restrictions. The Amen_2 fixed-price theorem is a corollary.
The implication is one-way, not an expression for the full cost in terms of pairs.

```sh
python3 scripts/replay_cyclic_sections.py
python3 tools/cairn.py check --json
python3 tools/cairn.py why fpbs-two-generator-action-cost-witness --json
```

The finite replay checks cyclic-section graphings and exact normalization only.
No formal verification, novelty, or universal solution is asserted.


## Arbitrary-subrelation and finite-phase repair (September 9, 2026)

Read `research/artifacts/phase-repair.md`. The continuation proves an exact
correlated-error torsion repair budget for arbitrary target subrelations. It
also separates zero finite-index repair cost from the exact cost restoration
caused by single-phase selection. No universal conjecture or odd-exponent
Burnside fixed-price assertion is marked solved.

```sh
python3 scripts/replay_phase_repair.py --output research/artifacts/phase-repair-checks.json
python3 tools/cairn.py check --json
python3 tools/cairn.py why fpbs-burnside-low-cost-averaged-connector-target --json
```

The replay is standard-library finite combinatorics. The new note rederives the
needed subgroup detour and common-upper-cost argument; other historical claims
are retained as provenance, not independently revalidated. Cairn ESTABLISHED
means a recorded proof route, not an externally certified mathematical theorem.


## Adaptive repair and the hyperfinite connector obstruction

Read `research/artifacts/connector-capacity.md` for the new deductions and explicit limitations. The adaptive overlap theorem, variable-order consequence, and uniform hyperfinite defect barrier have written proofs, not independent or formal verification. A low-cost Burnside construction remains OPEN, as do both universal goals. Prior nodes are retained as provenance and have not all been re-audited.

```sh
python3 scripts/replay_connector_capacity.py --output research/artifacts/connector-capacity-checks.json
./bin/cairn check --json
```

The replay checks exact finite algebra and repaired connectivity only.

## Fractional-cut repair and near-cost-one seeds

Read `research/artifacts/cut-repair.md`. This addition proves a fractional-cut repair
criterion, an explicit strict separation from the earlier whole-path second moment,
and exact low-cost seed constructions from the published Gaboriau-Lyons and
Miller-Tserunyan theorems. The seed/network fitting problem remains OPEN, as do
both universal goals. Earlier proof notes are provenance, not re-audited premises.

```sh
python3 scripts/replay_cut_repair.py --output research/artifacts/cut-repair-checks.json
./bin/cairn check --json
./bin/cairn why fpbs-cut-burnside-network-target --json
```

Exact finite tests and high-precision or numerical-LP benchmarks are reported separately.
Neither is a formal verification of the infinite mathematics.
