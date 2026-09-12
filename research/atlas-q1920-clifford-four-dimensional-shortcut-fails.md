---
rg: 2
id: atlas-q1920-clifford-four-dimensional-shortcut-fails
kind: claim
title: Minimal chief-factor irreducibility does not force the Q1920 seam packet to have dimension four
artifacts:
  - experiments/atlas_a4_q1920_f3_module_fixed_spaces.g
  - research/artifacts/atlas-a4-q1920-f3-module-fixed-spaces.json
distinct_from:
  atlas-no-perfect-solvable-a5-action-on-f3-four-space: that closes every perfect solvable-by-A5 action image in dimension four; this proves that higher-dimensional local modules remain logically possible.
  atlas-q1920-solvable-kernel-forces-small-f3-chief-factor: that bounds the A5-cyclic span of z; this distinguishes that span from the full L-chief factor.
---

Let `E` be a minimal `L`-chief factor on which `z` survives and put
`W=<z^A5>`.  Minimality makes `E` irreducible as an `F3[L]` module, but it does
not make `W` `L`-invariant: the complement `A5` is not normal in `L`.
Consequently Clifford transitivity for a normal subgroup cannot be applied to
deduce `E=W`.

This is not merely a formal warning.  For both marked local groups
`Q=Q1920`, exact modular representation calculation finds nonzero fixed
spaces for the marked radial `A=S3` inside faithful irreducible
`F3[Q]` modules of dimensions

```text
6, 10, 24.                                                 (Q1920-CLIFF-1)
```

For the first marking the faithful profiles

```text
(dimension, A-fixed, B-fixed) = (6,2,0), (10,3,1),
                                 (10,1,3), (24,4,4)
```

occur; the second marking swaps the two six-dimensional radial orientations
and has the same ten- and twenty-four-dimensional profiles.  Thus an
`A`-fixed candidate vector for `z` can generate a local `Q`-packet strictly
larger than the four-dimensional `A5` constituent.

## Attempts

The perfect-action classification in `GL4(3)` closes the four-dimensional
case completely, but `(Q1920-CLIFF-1)` prevents promoting it to all solvable
kernels by minimality alone.  The next exact problem is finite-dimensional:
for each marked module in `(Q1920-CLIFF-1)`, determine whether there is an
involution `C` centralizing the marked `A`, satisfying the collision word and
`(CT)^3=1`, whose minus-one eigenspace meets the `A`-fixed space nontrivially.
