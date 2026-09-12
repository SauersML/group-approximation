---
rg: 2
id: literal-fiber-unequal-reflection-row-collapses-packet
kind: claim
title: A same-object unequal-reflection row collapses an injected literal packet fiber
distinct_from:
  btb-balanced-loops-stop-at-same-object-reflection: That leaves a same-object support row as the first relation outside the rectangular-Weyl countermodel; this proves that realizing both supports as literal unequal-trace finite-packet projections destroys packet injection.
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: That proves the finite-matrix rank floor for Leavitt coarse/fine corners; this proves why those corners cannot both be authenticated as fixed group-algebra projections in the canonical regular trace.
  literal-antiphase-branches-recreate-regular-character-packing: That treats many orthogonal literal translates; this treats one conjugacy between two literal corners of unequal canonical trace.
---

**ESTABLISHED REGULAR-TRACE FENCE.**  Let `H` be a finite subgroup injected
in a group `G`, and let `q,e,f in C[H]` be projections with `e,f<=q`.  If a
word `W in G` satisfies

```text
W q W^*=q,                 W e W^*=f,                   (LUR1)
```

then

```text
tau_H(e)=tau_G(e)=tau_G(f)=tau_H(f).                    (LUR2)
```

Here the restriction of the canonical group trace to `C[H]` is the canonical
finite-group trace because `H` is injected, and the middle equality is
tracial invariance.  Consequently `(LUR1)` is impossible when the two literal
corners have unequal finite-packet trace.

The reflection form is identical.  If

```text
R_e=1-2e,             R_f=1-2f
```

are authenticated group words and the presentation imposes

```text
R_f W R_e W^*=1                                      (LUR3)
```

on the same `q`-object, then `(LUR3)` gives `WeW^*=f` and `(LUR2)` applies.
For the binary Leavitt coarse/fine dimensions, the traces are respectively
`tau(q)/2` and `tau(q)/4`, so a nonzero injected literal `q` cannot support
this row.

This closes the tempting direct use of the literal BTB root fiber in `(BAF3)`.
One may tensor the root fiber with finite `M_2` and `M_4` packets and obtain
literal coarse and fine projections, but a stable letter preserving that
fiber cannot conjugate them without collapsing the packet type.  If the
stable letter is allowed to move the fiber, the complementary packet sectors
supply exactly the regular-trace compensation and the compressed same-object
rank argument no longer applies.

The result does not rule out a genuine Leavitt/index compiler.  In the
properly infinite coefficient model the coarse and fine idempotents are
equivalent even though finite matrices cannot realize them on one reservoir.
But they are not fixed projections of `C[G]` in the group regular
representation.  A successful compiler must therefore decode their common
finite-matrix carrier from non-semisimple Steinberg/Leavitt word data.  That
is the finite-coordinate interface of
`affine-leavitt-prescribed-root-spectral-carrier-decoder`, now with the
literal BTB fiber available as the prescribed carrier; literal finite packets
do not bypass it.

DERIVATION
canonical-trace-forbids-literal-unequal-corner-conjugacy
