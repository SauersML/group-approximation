---
rg: 2
id: simple-group-classical-width-finite-field-linear-soficity
kind: claim
title: A finitely presented simple group not linear sofic over finite fields has bounded relator width over all symplectic, unitary and orthogonal groups
distinct_from:
  simple-group-psl-width-is-finite-field-linear-soficity: that proves the special linear family and the converse; this is the symplectic, unitary and orthogonal families, which need class-size bounds from the fixed space and a commutator choice inside the isometry group.
  non-linear-sofic-simple-groups-bounded-width-in-classical-groups: that is the open fixed-field statement for all four families with a field-dependent constant; this proves the three isometry families with a constant uniform in the rank and in the field.
  simple-group-relator-width-in-finite-simple-targets: that covers bounded rank, sporadic, symmetric and alternating targets; this covers unbounded rank isometry groups.
---

**OPEN (proof in progress, lane `ex-weak-sofic-classical-covering`).** Let `G = <X | R>` be an infinite
finitely presented simple group that is not linear sofic over finite fields (definition on
`simple-group-psl-width-is-finite-field-linear-soficity`). Then there is `K = K(G)` with `w_Q(a) <= K`
for every `a in Q^X`, and every `Q = Q_0/Z_0`, where:
- `Q_0` is `Sp_n(q)`, `SU_n(q)` or `Omega^+-_n(q)`, for any `n` and `q`;
- `Z_0` is central.

With "not `F_p`-linear sofic" in place of the hypothesis, the same holds uniformly over all `q = p^e`.

**Payoff.** With `simple-group-psl-width-is-finite-field-linear-soficity` and
`simple-group-relator-width-in-finite-simple-targets`, the relator width of a finitely presented simple
group is bounded over **all** finite simple groups iff the group is not linear sofic over finite fields.
Sofic groups are linear sofic over every field. So the classical escape from
`fg-simple-weakly-sofic-groups-are-sofic` is exactly linear soficity over finite fields.

## Attempts

- **Part 1, established (artifact).**
  `research/artifacts/classical-relator-width-part1-class-sizes-2026-09-13.md`, all elementary:
  - hyperbolic splitting over finite fields;
  - counts of singular vectors;
  - `|Q_0| >= q^(dim - O(n))` from the big cell `U^- x SL_m x U`, whose factors lie in `I(V)'`;
  - a fixed-space stabilizer count.

  Result: if `k in I(V)` has `s = rk(k - 1) <= n/4`, then `|k^(Q_0)| >= (1/4) q^(s n/2 - 3n - 4)`.
- **Part 2, planned: commutator choice.** For `h in I(V)` with `rho(h) >= eta n`, build a hyperbolic
  subspace `Y` of dimension `2r'`, with `r' ~ eta n/6`, by greedy hyperbolic pairs, so that
  `dim(Y + hY) >= 3 r'`. Take `y = m(C_p) (+) 1`, with `C_p in SL_(r')(q)` a companion matrix without
  eigenvalue `1`. Then `[h, y]` has rank between `r'` and `4 r'`.
- **Part 2, planned: localization.**
  - A near-central tuple of isometries lies in `I(W) x 1` for a nondegenerate `W` with
    `dim W = O(max_x rho(a_x))`.
  - The displacement is a product `s s'` of two conjugate swap involutions, so it lies in `I(V)'`.
  - The template uses double commutators (`G = G''`). This keeps every covered element inside `Q_0`,
    with no spinor-norm or determinant corrections.
- **Part 3, planned: assembly.** It follows `simple-group-psl-width-is-finite-field-linear-soficity-proof`
  Sections 3 to 5 in three regimes:
  - proportional support;
  - large local dimension;
  - bounded local dimension, by minimal degrees.
