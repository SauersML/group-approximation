---
rg: 2
id: binary-leavitt-three-row-atomic-compiler
kind: claim
title: Compile three bounded prototype rows into one returned binary Leavitt atom
distinct_from:
  opnorm-leavitt-coarse-fine-return-row: that authenticates a coarse M2 packet, a fine M4 packet and a support row; this may bypass both packet exactifications and must output only the two inverse rows and completeness row on the prescribed root atom.
  leavitt-steinberg-bounded-area-carmichael-lift: that seeks uniformly bounded fillings for an unbounded Thompson Carmichael family; this permits a coordinate-dependent address of arbitrary length but insists that the three semantic discrepancies be literal conjugates of finitely many prototypes.
artifacts:
  - research/binary-leavitt-atomic-return-via-three-row-compiler.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

**OPEN.** In the finite presentation of
`St_20(L_(F_2)(1,2))`, find finitely many fixed prototype discrepancy words
`q_1,...,q_N`, a constant `C`, and a finite-matrix selection rule with the
following property.

Whenever the rounded nontrivial spectral atom `p_U` of `z=x_13(s_1t_1)` is
nonzero, the rule may inspect the matrix coordinate and select an arbitrary
Leavitt address and finite coefficient window.  It must then produce four
operators in `p_U M_d(C)p_U` for which each of

```text
t_0s_0-p_U,
t_1s_1-p_U,
s_0t_0+s_1t_1-p_U
```

has operator norm at most

```text
C max_j ||q_j(U)-1||_op.                               (BAC1)
```

Every check at the selected address must be a literal unitary conjugate of a
prototype, so its defect is independent of address length.  This formulation
allows the depth and window to depend on the actual matrix dimension without
asking for a full multiplication table or a coherent inverse-limit module.

## Attempts

The obvious depth-one prefix word does not work: its exact typed rectangular
model swaps equal minimal corners while leaving the two packet identities
unidentified.  Adding fixed typed Steinberg triangles, PI tests, Reynolds
ranks, or finite semisimple packet multiplicities still admits the same
escape.  The nearest operator-norm tools are
`conjugacy-addressed-opnorm-challenges-are-lossless` and
`opnorm-coordinatewise-capacity-diagonal`; neither currently constructs the
cross-typed additive completeness row.  A concrete next probe is to close
off-diagonal loops through the depth-one chart and test whether finitely many
loop discrepancies control the operator sum of the returned range
projections on `p_U`.

