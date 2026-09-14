---
rg: 2
id: central-local-data-of-incidence-girth-twelve-keeps-the-phase
kind: claim
title: Finite local data whose incidence graph has girth at least twelve and whose variable subgroups meet pairwise in the phase keep the phase at full order, for arbitrary nonabelian local groups
artifacts:
  - research/artifacts/hl-nh-local-colimit-2026-09-13.md
distinct_from:
  slofstra-zhang-high-girth-phase-survival: that proves survival for abelian solution groups of linear systems through planar pictures under degree and girth bounds; this proves survival for arbitrary finite nonabelian local groups and arbitrary Boolean constraints, through developability of a nonpositively curved complex of groups.
  barycentric-curvature-certificates-need-incidence-girth-eight: that gives a necessary cycle length for any barycentric curvature certificate; this gives a sufficient condition, at girth twelve with central pairwise intersections.
  finite-readout-bcs-decoders-are-phase-surviving-local-colimits: that reduces decoders to phase survival in the local colimit; this certifies survival for a large class of local data, so that for such data a decoder exists.
---

**ESTABLISHED** by `central-local-data-girth-twelve-phase-via-cone-metric`.
Not independently reviewed. No novelty is claimed: the metric and the link
computation are those of Prytula's proof for graphical complexes of groups,
applied with the phase at the cone vertex.

## Statement

Let `D` be finite local data for a Boolean constraint system `B` and `n`, as in
`finite-readout-bcs-decoders-are-phase-surviving-local-colimits`, with
context groups `A_c`, variable groups `H_v` and central phase `J = Z/n`.
Assume:

1. **(G12)** every cycle of the incidence graph `Inc(D)` has length at least
   `12` (at least six contexts);
2. **(CI)** in every context group, distinct variable subgroups meet only in
   the phase: `H_v cap H_w = J` for `v != w` in `V_c`;
3. **(PR)** all inclusions are proper: `J < H_v < A_c` for `v in V_c`.

Then every local group, in particular `J`, injects into the local colimit
`Lambda(D)`. So `J` has order exactly `n` in `Lambda(D)`, and by (LC1) the
readouts give an exact finite-readout decoder
`A(B) -> C[Lambda(D)] p_omega`.

No degree bound, no abelian hypothesis and no condition on the constraints is
used, beyond what (CI) and (PR) say about the subgroups.

## Remarks

- **Consistency with the necessary bound.** For nonscalar readouts,
  `barycentric-curvature-certificates-need-incidence-girth-eight` needs at
  least four contexts per cycle. This theorem uses six, with the same
  barycentric complex and the angles `pi/3, pi/2, pi/6`.
- **Calibration against linear systems (`n = p = 2`).** Take a linear system
  over `Z_2` with at least three variables per equation, local groups
  `A_c = <J, x_v : v in V_c | commuting involutions, prod x_v = J^(b_c)>` and
  group-element readouts `x_v p_omega`. The subgroups `<J, x_v>` meet pairwise
  in `J`, so (CI) holds.
  - In the hypergraph `H(A)` of Slofstra--Zhang, the vertices are equations and
    the edges are variables. A Berge cycle of length `k` is an incidence cycle
    of length `2k`, and "minimum vertex degree >= 3" means at least three
    variables per equation.
  - So this theorem recovers `|J| = 2` in the solution group whenever `H(A)` has
    girth at least 6 and minimum degree at least 3. That is the `(3,6)` case of
    `slofstra-zhang-high-girth-phase-survival` for `p = 2`.
- **Why (CI) cannot be dropped.** In the cyclic system of arbitrary length where
  each equation `x_(e_(i-1)) x_(e_i) = J^(b_i)` has two variables and
  `sum b_i` is odd, `J` dies. There each readout is a function of its
  neighbour, so (CN2) of `commuting-nonscalar-readouts-force-coset-four-cycles`
  makes `H_(e_(i-1)) cap H_(e_i)` strictly larger than `J`, and (CI) fails.
- **Consequence for the MIP* route.** Survival is automatic for local data
  satisfying (G12), (CI), (PR). What stays hard is constructing such local data
  for a non-`R^U` source, since functional subdivision cannot raise the
  incidence girth (CB3); see `some-nonru-bcs-has-central-local-data-of-girth-twelve`.
