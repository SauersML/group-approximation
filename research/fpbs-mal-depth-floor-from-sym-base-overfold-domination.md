---
rg: 2
id: fpbs-mal-depth-floor-from-sym-base-overfold-domination
kind: route
title: The Bernoulli floor follows from one finite statement, that overfold merges save at most a bounded factor on transitive covers of the Cayley level of Sym(j+2), where every overfold seed is cross-orbit; the density witness is a tower over that level
target: fpbs-mal-bernoulli-single-stage-floor
requires:
  - fpbs-mal-floor-iff-deep-promotion-floor
  - fpbs-mal-promotion-cost-monotone-under-weak-containment
  - fpbs-mal-depth-promotion-equals-overfold-merge-number
  - fpbs-mal-sym-levels-embed-orbits-at-every-depth
  - fpbs-mal-seed-density-towers-over-orbit-gapped-bases
  - fpbs-mal-overfolds-dominated-on-sym-base-covers
artifacts:
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/eb_family.py
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/family_d4_d10.txt
  - experiments/fpbs-overfold-embedded-orbits-2026-09-17/cayley_blocks.py
---

Notation is as in [[fpbs-mal-depth-promotion-equals-overfold-merge-number]].
`ρ` is the Bernoulli shift of `L`. `B_j` is the Cayley level of `Sym(j+2)`,
with `a ↦ (0 1)` and `b ↦ (0 1 ⋯ j+1)`.

**Relation to `fpbs-mal-depth-floor-from-overfold-domination`.** That route
has the same target and the same first three steps. It uses the tower over a
point and needs the exchange statement `fpbs-mal-overfold-merges-never-help`
on **every** level of that tower, including the within-orbit overfolds. This
route replaces the witness by a tower over `B_j`. On that tower every
overfold seed is cross-orbit, and every `L_j`-orbit lies over a two-point
orbit of `B_j`. The only open premise is then
[[fpbs-mal-overfolds-dominated-on-sym-base-covers]], which is implied by
the open premise of the other route and is strictly narrower.

1. By [[fpbs-mal-floor-iff-deep-promotion-floor]], the target holds iff
   `inf_j Q_j(ρ) > 0`.
2. Fix `j`. By item 4 of [[fpbs-mal-sym-levels-embed-orbits-at-every-depth]],
   every `L_j`-orbit of `B_j` has two points, on which `a` and `t_j` act as
   the same swap, so `μ_j(B_j) = −1`. By
   [[fpbs-mal-seed-density-towers-over-orbit-gapped-bases]] with
   `λ_0 = 0.9`, there is an essentially free profinite action
   `X_j = lim Q_m` of `L` with `Q_0 = B_j`, every level a transitive cover of
   `B_j`, and `r(Q_m^{(j)}) ≥ |Q_m|/60` for every `m`.
3. By the depth costs of
   [[fpbs-mal-promotion-cost-monotone-under-weak-containment]] (Theorem M),
   `Q_j(c') ≤ Q_j(ρ)` for every free action `c'`. So `Q_j(ρ) ≥ Q_j(X_j)`.
   The witness may depend on `j`.
4. By item 4 of [[fpbs-mal-depth-promotion-equals-overfold-merge-number]],
   `Q_j(X_j) = inf_m deep_j(Q_m)/|Q_m|`. This uses only that `X_j` is
   essentially free and profinite with transitive levels.
5. Each `Q_m` is a finite transitive cover of `B_j`. By
   [[fpbs-mal-overfolds-dominated-on-sym-base-covers]],
   `deep_j(Q_m) ≥ c_1 · law_j(Q_m)`, with `c_1` independent of `j` and `m`.
   By item 2 of the depth node, `law_j(Q_m) = r(Q_m^{(j)})`. So
   `Q_j(X_j) ≥ c_1 · inf_m r(Q_m^{(j)})/|Q_m| ≥ c_1/60`.
6. So `Q_j(ρ) ≥ c_1/60` for every `j`. By step 1, the target holds. ∎

**Where it can fail.** Only step 5 is open.
- It fails if, for some sequence of depths `j`, transitive covers of `B_j`
  have cross-orbit overfold merge sets smaller than `law_j` by a factor that
  grows with `j`.
- Such a failure need not refute the target. The target needs `c_1` only on
  the particular towers of step 2, not on every cover of `B_j`. It could also
  be rescued by another base, since
  [[fpbs-mal-seed-density-towers-over-orbit-gapped-bases]] accepts any
  transitive base with `μ_j ≤ λ_0`.
- By the cover monotonicity remark in the (O|B) node, one bad level of a
  tower makes every level above it bad. So a counterexample to step 5 on a
  small cover of `B_j` would kill every tower through it. It would not by
  itself kill the route, which would then need towers avoiding such covers.

**Evidence for step 5.** On `B_2` and `B_3` themselves, the exact block
tests recorded in the (O|B) node find no block with
`deepc < Σ law`. No proper cover has been tested.

**Downstream.** With `fpbs-mal-floor-gives-fixed-price-counterexample`, this
is a route to `fpbs-fixed-price-counterexample-exists` whose only open
premise is the single finite statement (O|B).
