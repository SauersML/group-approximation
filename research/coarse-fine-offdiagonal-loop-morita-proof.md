---
rg: 2
id: coarse-fine-offdiagonal-loop-morita-proof
kind: route
title: Proof that the complete off-diagonal prefix chart remains Morita typed
target: coarse-fine-offdiagonal-loops-are-morita-blind
requires: []
---

Use the reversed dual-prefix convention.  Cancellation gives, for every
depth-two word `u`, depth-two word `v`, and letters `i,j`,

```text
t_u s_v=delta_(u,v),             t_i s_j=delta_(i,j).
```

Substitution in `(CFL1)` proves `(CFL3)`.  Inserting the coarse or fine
matrix unit between the same bridges proves `(CFL2)`.  Induction on path
length now reduces every composable path to its endpoint matrix unit and
every noncomposable path to zero.  Ordinary Steinberg commutator triangles
record exactly the same multiplication, so pasting them adds only
associativity.

For the finite model label the standard basis of `F_2^6` by

```text
C_0,C_1,F_00,F_01,F_10,F_11.
```

Map an arrow from label `b` to label `a` to the standard matrix unit
`E_(a,b)`.  The identity `E_(a,b)E_(c,d)=delta_(b,c)E_(a,d)` verifies the
entire path table.  The two typed identities are the orthogonal diagonal
projections displayed in `(CFL5)`.  Their difference is diagonal with
eigenvalues `1,1,-1,-1,-1,-1`, and hence has operator norm one after scalar
extension to `C`.

The exact arithmetic audit is
`experiments/coarse_fine_offdiagonal_loop_audit.py`.  It checks all `256`
instances of the forward/reverse three-factor paths and the two-factor
turns, then prints the two ranks and the diagonal of the carrier difference.
