---
rg: 2
id: leavitt-root-fixed-projections-equal-the-global-fixed-projection
kind: claim
title: Every core root subgroup has the full Leavitt group's fixed projection in a tracial representation
distinct_from:
  degree-zero-leavitt-core-characters-are-dirac-haar-mixtures: That classifies all core characters using a finite-group character estimate; this derives equality of root and whole-group fixed projections directly from conjugacy in the ambient Leavitt group, without any core-character classification input.
  binary-leavitt-elementary-group-is-simple: That is the group-theoretic simplicity input; this identifies invariant projections and the exact trivial weight of every tracial representation.
artifacts:
  - research/artifacts/leavitt-root-projections-and-elementary-character-proof-2026-09-08.md
---

Use the depth-two identification `H=L_(F_2)(1,2)^x=EL_4(R)`, let
`R_0` be the degree-zero coefficient ring, and set
`U_ij=x_ij(R_0)` for `i!=j`, `u=x_12(1)`.

In the finite tracial GNS algebra `(pi,M,tau)` of any character
`phi` of `H`, every `U_ij` has the same fixed projection `P`.
This is exactly the projection onto the fixed vectors of all of `H`,
and

```text
P in Z(M),       pi(g)P=P for every g in H,
tau(P)=phi(u) in [0,1].
```

The proof compares root groups with their same-row and same-column
elementary abelian overgroups. Every nonidentity element of those
groups is conjugate to `u` in `H`, so their nested fixed projections
have equal faithful trace. A spare root index gives centrality.

On the complementary central summand the character of `u` is zero.
The artifact also proves directly, using split row shears and proper
prefix corners, that this forces the entire complementary character
to be regular. Thus it supplies the full formula
`phi=phi(u)*1+(1-phi(u))*delta_1` without a finite-core character
theorem. This is a written proof; no new Lean verification or
nonhyperlinearity conclusion is asserted.
