---
rg: 2
id: finite-chord-joint-table-collision-proof
kind: route
title: Match all simultaneous spectral blocks and use one common-fiber free-phase rotation
target: finite-chord-context-is-joint-table-plus-collision
requires:
  - sequential-marginal-holonomy-is-conditional-rank-matching
  - feasible-chord-collision-has-free-phase-block-escape
  - free-phase-context-escape-criterion
---

Necessity of pairwise commutation of the `z_j` follows by conjugating the
commuting source tuple.  If `U` satisfies `(FCC1)`, it commutes with every
`e_omega` and carries each source joint spectral projection in `(FCC2)` onto
the corresponding target one, so their ranks agree.

Conversely, decompose `C^D` over the mutually orthogonal projections

```text
e_omega product_j p_(epsilon_j)(x_j).
```

The commuting target tuple gives the analogous orthogonal decomposition.
Equation `(FCC2)` supplies equal dimensions block by block.  Choose a unitary
between each corresponding pair and take their direct sum.  It commutes with
the frozen `d_i` and intertwines every sign simultaneously, proving `(FCC1)`.
This is the finite joint-table form of iterated conditional rank matching;
the full table is precisely the compatibility condition between iterations.

After conjugating the context PVM by `U`, refine it into rank-one coordinates
jointly diagonal for `(FCC3)`.  On collided lines `e_s<=UP_aU*` and
`e_t<=UP_bU*`, `a!=b`, take a Hadamard `H_st`.  With independent free
generators `h_j`, put

```text
W=sum_j e_j tensor h_j,                 V=W H_st.       (FCP1)
```

Exactly as in `feasible-chord-collision-has-free-phase-block-escape`, `V`
commutes with `(FCC3)` and the two coarse assignment projections retain
nonzero coefficients at the reduced words `h_s h_t^-1` and `h_t h_s^-1`.
They therefore leave the root block, while the same final partition supplies
all target marginals.

If there is no collision, every context atom is a joint spectral projection
of `(FCC3)`.  Its commutant fixes every atom by
`free-phase-context-escape-criterion`.  This proves necessity and completes
the fixed-target classification.  Notice that the direct-sum construction
does not select target tuples at adjacent contexts; imposing all edge choices
at once is the remaining global holonomy constraint.

