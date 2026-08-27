---
rg: 2
id: join-tree-signed-hecke-induction-proof
kind: route
title: Attach child context blocks with fresh commuting free phases
target: join-tree-bcs-has-explicit-signed-hecke-atlas
requires:
  - tracial-bcs-rationalizes-full-overlap-distributions
  - one-binary-marginal-block-escape
  - free-phase-context-escape-criterion
---

Start with the root context in `q_D C[K_D]q_D=M_D(C)`.  Inductively suppose
the parent context is a transported matrix block `M_p` with coordinate matrix
units `(E^p_(ij))`.  The full-overlap rank equalities give a permutation
unitary `v in M_p` carrying the child's separator signs to the already fixed
parent signs.

Within each joint separator fiber choose a further unitary `u`.  When two
supported child assignments occupy one fiber, take a Hadamard plane crossing
those assignment blocks; otherwise take the identity.  Both `u` and `v`
commute with the transported separator tuple after the identification.

Pass from the current group `Gamma_0` to `Gamma_0 times F_D`.  Its free
generators commute with every element of `C[Gamma_0]`.  Therefore

```text
W=sum_i h_i E^p_(ii)                                     (JTA2)
```

is a corner unitary by the same calculation as `(OBM5)`.  Define the child
matrix block by conjugating `M_p` with `Wuv`, and define its assignment atoms
by the prescribed sums of its coordinate atoms.  Because `W` is diagonal in
the parent coordinates and `u` is block diagonal over separator fibers, every
separator sign is fixed.  The child's other signs are defined by its own
assignment labels, so all of its predicate relations hold.

For a rooted join tree,

```text
U_c intersect (union of earlier U_d) subset U_c intersect U_p. (JTA3)
```

Indeed a previously seen context containing `x in U_c` is joined to `c` by a
path whose first vertex is `p`, and connectedness of the `x`-contexts forces
`x in U_p`.  Thus preserving the parent separator establishes every required
old overlap.  Finite iteration proves the claim.
