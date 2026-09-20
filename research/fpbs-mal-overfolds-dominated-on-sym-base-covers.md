---
rg: 2
id: fpbs-mal-overfolds-dominated-on-sym-base-covers
kind: claim
title: There is c_1 > 0 such that for every j and every finite transitive F(a,b)-set Q covering the Cayley level of Sym(j+2), overfold merges save at most a factor c_1, deep_j(Q) >= c_1 law_j(Q); on such Q every overfold seed joins two different L_j-orbits
distinct_from:
  fpbs-mal-overfold-merges-never-help: that asks deep_j >= c_1 law_j (or equality) on every finite Q, including within-orbit overfolds; this asks it only on transitive covers of B_j = Cay(Sym(j+2)), where every overfold seed is cross-orbit. That claim implies this one.
  fpbs-mal-sym-levels-embed-orbits-at-every-depth: that is the established structural fact forcing overfolds on covers of B_j to be cross-orbit; this is the open inequality on those covers.
  fpbs-mal-seed-density-towers-over-orbit-gapped-bases: that gives law_j >= |Q|/60 on some tower over B_j; this compares deep_j with law_j on all covers of B_j.
artifacts:
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/blocks.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/cayley_blocks.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/blocks_sym4_j2_b2.txt
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/blocks_sym4_j2_b3.txt
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/blocks_sym4_j2_b4.txt
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/blocks_sym5_j3_b2.txt
  - experiments/fpbs-overfold-exact-c-2026-09-17/deep.c
---

**OPEN.** Notation is as in
[[fpbs-mal-depth-promotion-equals-overfold-merge-number]] and
[[fpbs-mal-overfold-merges-never-help]]. `B_j` is the Cayley level of
`Sym(j+2)`, with `a ↦ (0 1)` and `b ↦ (0 1 ⋯ j+1)`. A *cover* of `B_j` is a
finite `L`-set `Q` with an `L`-equivariant map onto `B_j`.

Prove that there is `c_1 > 0` such that, for every `j ≥ 0` and every finite
transitive cover `Q` of `B_j`,

```text
deep_j(Q)  ≥  c_1 · law_j(Q)      ( law_j(Q) = r(Q^{(j)}) ).
```

**Why it matters.** It is the only open premise of the route
`fpbs-mal-depth-floor-from-sym-base-overfold-domination` to
`fpbs-mal-bernoulli-single-stage-floor`. The other premises are
established:
- [[fpbs-mal-seed-density-towers-over-orbit-gapped-bases]] gives, for each
  `j`, a tower of transitive covers of `B_j` with `law_j ≥ |Q_m|/60`;
- Theorem M and the depth node turn `deep_j ≥ c_1 law_j` on that tower into
  `Q_j(ρ) ≥ c_1/60`.

It is implied by `fpbs-mal-overfold-merges-never-help`. It is strictly
narrower in two ways:
- **Cross-orbit only.** By item 3 of
  [[fpbs-mal-sym-levels-embed-orbits-at-every-depth]], every cover `Q` of
  `B_j` satisfies (E). So every overfold seed on `Q` joins the fibres of two
  **different** `L_j`-orbits. Within-orbit overfolds do not occur.
- **Orbits over two points.** Every `L_j`-orbit of `Q` covers a two-point
  orbit `{g, gα}` of `B_j` on which `a` and `t_j` act as the same swap.

**Reduction to blocks.** A seed set `P` splits by which orbits its seeds
join. For a set `W` of `L_j`-orbits, let `deepc(W)` be the least number of
seeds, each lawful inside an orbit of `W` or cross-orbit between two orbits
of `W`, whose closure collapses `ker(m)` over all of `W`. Under (E), a
minimum promoting set is a disjoint union of such blocks. So
`deep_j(Q) = min Σ_W deepc(W)` over partitions of the orbits into blocks,
and `law_j(Q) = Σ_O law(O)`. The claim fails with `c_1 = 1` exactly when
some block has `deepc(W) < Σ_{O∈W} law(O)`.

**Evidence (exact, on the base itself).** `cayley_blocks.py` runs the exact
solver `deep.c` of `fpbs-overfold-exact-c-2026-09-17` on blocks containing
the orbit of the identity. Left multiplication by `Sym(j+2)` permutes the
orbits transitively and preserves everything, so this covers every block up
to symmetry. On `B_j` each orbit has `law = 1`. So a counterexample block of
`b` orbits would collapse with at most `b − 1` seeds.
- `B_2` (`n = 24`, 12 orbits):
  - all 11 two-blocks have `deepc = law` (`blocks_sym4_j2_b2.txt`);
  - all 55 three-blocks have `deepc = law` (`blocks_sym4_j2_b3.txt`);
  - 83 of the 165 four-blocks, recorded in `blocks_sym4_j2_b4.txt`, all
    have `deepc = law`. This run was stopped by hand after 83; the other 82
    are untested.
- `B_3` (`n = 120`, 60 orbits): all 59 two-blocks have `deepc = law`
  (`blocks_sym5_j3_b2.txt`). The blocks have up to 66 seed candidates, most
  of them cross-orbit.

No computation has yet been done on a proper cover of `B_j`. These are the
instances that matter, since the density witness lives on covers.

**Remark (monotone along covers, not used).** If `Q̃ → Q` is an `N`-sheeted
cover, then `deep_j(Q̃) ≤ N·deep_j(Q)` and `law_j(Q̃) ≤ N·law_j(Q)`.
- Lift each seed `(v, v')` over `q` to its `N` lifts over the points above
  `q`.
- Propagation along equally labelled edges, and transitivity inside a
  fibre, both lift fibrewise. So the closure of the lifted set contains
  every lift of every pair in the closure.
- Every pair of `ker(m̃)` is a lift of a pair of `ker(m)`, because `m` is
  induced by the morphism `C_{j+1} → C_j`.

So along a tower of covers the densities `deep_j/|Q_m|` are non-increasing,
and the infimum in item 4 of the depth node is a limit. In particular, one
bad level makes every level above it bad.
