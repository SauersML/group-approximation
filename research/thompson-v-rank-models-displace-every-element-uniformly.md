---
rg: 2
id: thompson-v-rank-models-displace-every-element-uniformly
kind: claim
title: In every rank model of Thompson's V, each nontrivial element displaces at least a quarter of a cylinder 3-cycle
distinct_from:
  thompson-v-rank-models-through-displacing-sym-reps-are-trivial: that works at finite stages through symmetric-group representations, where relator errors are group elements; this works in the ultraproduct itself, for every rank model, and gives a uniform lower bound rather than triviality.
  thompson-v-cantor-system-has-no-covariant-rank-model: that excludes models carrying a covariant cylinder algebra; this constrains every model without reference to the cylinder algebra.
---

**ESTABLISHED** (route `thompson-v-uniform-displacement-commutator-proof`).

Let `sigma : V -> M^x` be a homomorphism into a rank ultraproduct over any field. Let `t` be a cylinder
3-cycle, a prefix replacement cycling three disjoint cylinders whose union is not all of `X`. All such
elements are conjugate in `V`, so `d_3 = rk(sigma(t) - 1)` does not depend on `t`. Then:
- `rk(sigma(z) - 1) >= d_3/4` for every `z != 1` in `V`;
- `d_3 > 0` if and only if `sigma` is nontrivial.

**Why it matters.**
- A nontrivial rank model of `V` is uniformly discrete. Displacement does not shrink with support:
  cylinder 3-cycles of every depth are conjugate, and every nontrivial element displaces at least a
  quarter as much as they do.
- The gate `thompson-v-has-no-nontrivial-f2-rank-model` says `d_3 = 0` in every characteristic-two
  model. Any counterexample carries this uniform bound.
- The bound does not decide the gate by itself. Honest representations of large symmetric groups
  satisfy the same inequality with `d_3 = 2/3`, for instance the regular module. Like the involution
  calibration in the gate's `## Attempts`, it is a necessary condition, not an obstruction.
