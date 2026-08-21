---
rg: 2
id: common-source-partial-isometries-decode-one-game-state
kind: claim
title: Separate context partial isometries with one initial projection decode one game state
distinct_from:
  partial-isometry-swap-wordizes-one-bcs-gram-row: that converts one intertwining row for one partial isometry to an ordinary commutator; this proves that the partial isometry may depend on the context as long as every context has the same initial projection.
  one-gram-vector-decodes-a-finite-bcs-strategy: that uses one literal matrix Gram operator in every context; this pulls different context ranges back to one common source Hilbert space and obtains the same finite-game gap.
  pairwise-cross-grams-do-not-supply-one-game-state: that gives an exact countermodel when the source state changes from edge to edge; this shows that different ranges are harmless and identifies the common initial projection as the actual load-bearing datum.
---

Let `B` be a fixed finite constraint-variable BCS game with

```text
omega^*(B)<=theta<1.                                   (CSI1)
```

For each context `c`, let `(P_(c,a))_a` be a PVM in a finite tracial
matrix algebra `(M,tau)`, put

```text
A_(c,x)=sum_a a_x P_(c,a),
F_c=sum_(a forbidden for c)P_(c,a),                    (CSI2)
```

and let `B_x` be a self-adjoint involution for each global variable.  Let
`Q` be a projection commuting with every `B_x`.  For every context choose a
partial isometry `S_c` with

```text
S_c^*S_c=Q,             P_c=S_cS_c^*,                 (CSI3)
```

and assume that `P_c` commutes with the context PVM.

Define the multi-range common-source energy

```text
E_Q=sum_(c,x) mu_(c,x)
 [ ||F_cS_c||_2^2
   +(1/4)||A_(c,x)S_c-S_cB_x||_2^2 ].                 (CSI4)
```

Then

```text
E_Q >= (1-theta)tau(Q).                               (CSI5)
```

Thus the finite-game argument does **not** require one identical Gram
operator or one identical controlled swap in every context.  Separate
context ranges, including orthogonal ranges, are permitted.  What must be
literal and common is only the initial projection `Q`.

## Proof

Work on the finite Hilbert space `Q C^d`.  The operators

```text
tilde P_(c,a)=S_c^*P_(c,a)S_c                         (CSI6)
```

form a PVM there.  Orthogonality follows from the context PVM and the fact
that its atoms reduce `P_c`; their sum is `S_c^*P_cS_c=Q`.  Bob restricts
the binary PVM of `B_x` to `Q C^d`, which is legal because `[B_x,Q]=0`.
Use the maximally entangled state on `Q C^d tensor conjugate(Q C^d)`.

The forbidden-answer probability is

```text
tau(S_c^*F_cS_c)/tau(Q)=||F_cS_c||_2^2/tau(Q).        (CSI7)
```

The pulled-back Alice involution is `S_c^*A_(c,x)S_c`.  Moreover

```text
S_c^*(A_(c,x)S_c-S_cB_x)
 =S_c^*A_(c,x)S_c-QB_x.                              (CSI8)
```

Left multiplication by `S_c^*` is contractive in normalized
Hilbert--Schmidt norm.  The usual maximally-entangled calculation therefore
bounds the bit-disagreement probability by

```text
||A_(c,x)S_c-S_cB_x||_2^2/(4 tau(Q)).                 (CSI9)
```

After averaging, the constructed strategy has loss at most
`E_Q/tau(Q)`.  The gap `(CSI1)` proves `(CSI5)`.  The case `Q=0` is
immediate.  ∎

## Consequence for the swap actuator

For each context, `partial-isometry-swap-wordizes-one-bcs-gram-row` turns
the two rows in `(CSI4)` into ordinary commutator-word defects using the
context's own reflection `J_(S_c)`.  Hence the analytic part of the static
game compiler only needs:

```text
one common initial projection Q,
one separately authenticated partial-isometry swap J_(S_c) per context.
                                                                    (CSI10)
```

The stronger requirement that every context use the same literal `S` or
the same literal swap is unnecessary.  This does not manufacture the
common `Q`; it strictly narrows the remaining finite packet/compiler task.

## Attempts

- **Use unrelated source projections.**  This is exactly the direct-sum
  countermodel in `pairwise-cross-grams-do-not-supply-one-game-state`; the
  proof above breaks because the pulled-back measurements live on different
  Hilbert spaces.
- **Require identical range maps.**  This works but is unnecessary.  The
  calculation `(CSI6)--(CSI9)` shows that all context dependence may remain
  in the ranges and in `S_c`.
- **Synchronize only source traces.**  Equal ranks do not identify the
  source state.  A literal common projection, or a separately proved
  common-coordinate synchronization theorem, is still required.
