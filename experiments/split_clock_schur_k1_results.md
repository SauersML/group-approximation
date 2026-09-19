# First finite split-clock Schur multiplier

Date: 2026-08-11

## Exact result

Take `p=3`, `k=1`, so `M=3`, `n=9`, and form the finite group

`G_1=J_1 semidirect (C_9 semidirect_4 C_3)`

from Theorem 5 of
`notes/FALSE_SPLIT_SQUARE_ZERO_H2_AMPLIFIER.md`.  In the augmentation basis

`a=e_1-e_0`, `b=e_2-e_0`,

the stable letter acts by

`a |-> b-a`, `b |-> -a`.

An exact polycyclic presentation therefore has generators `a,b,h,c`, orders
`9,9,9,3`, all of `a,b,h` commuting, and conjugation rules

`c h c^-1=h^4`,
`c a c^-1=b a^-1`,
`c b c^-1=a^-1`.

GAP converts this presentation to a pc group and certifies

`|G_1|=2187`,

`H_2(G_1;Z) ~= C_3 directSum C_3 directSum C_9`.       `(SCK1)`

Thus the first finite instance has Schur exponent `9`.  The family theorem
only requires divisibility by `p^k=3` at this stage, so `(SCK1)` is stronger
than the guaranteed lower bound.

## Scope

The result verifies the first closed-form finite group in the growing Schur-
curvature family.  It is not yet a quotient of the full Kun--Thom vertex, and
it does not establish vanishing curvature on the positive edge group.  Those
relative globalization conditions remain the main FALSE gate.

The assertion-based certificate is
`experiments/split_clock_schur_k1.g`.  It checks both the order and the full
Schur invariant-factor list.

