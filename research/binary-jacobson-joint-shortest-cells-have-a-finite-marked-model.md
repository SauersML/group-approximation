---
rg: 2
id: binary-jacobson-joint-shortest-cells-have-a-finite-marked-model
kind: claim
title: The two shortest Jacobson cells jointly have an exact finite marked model
artifacts:
  - research/binary-jacobson-joint-shortest-cells-finite-model-proof.md
  - research/artifacts/ptfree-sep7-jacobson-symbol-audit.md
distinct_from:
  binary-jacobson-first-mixed-kernel-is-three-syllable: that gives an explicit finite retraction after imposing only the controlled-swap cell; this asks for a finite model satisfying both shortest cells simultaneously.
  binary-jacobson-shortest-affine-braid-is-finite-marked: that gives an explicit GL-four model after imposing only the affine braid; neither earlier explicit model satisfies both cells required here.
  binary-jacobson-joint-shortest-cells-force-tail-action: that proves every marked model of the joint quotient must retain the tail factor; this asks whether such a finite marked model exists.
  binary-jacobson-joint-shortest-cells-exclude-natural-completions: that excludes natural head-plus-trivial-spectator completions; this asks for a finite model outside those excluded classes.
---

Retain the finite packet and overlap envelope

```text
F=G_Q x G_P,              Gamma_F=F *_K (K x <h>)
```

from `binary-jacobson-one-step-finite-type-envelope-is-marked-mf`, and impose
simultaneously the affine braid and controlled-swap cells

```text
(h w_23)^3=1,

(rho^2 h w_12 rho^(-2))(rho h w_12 rho^(-1))(h w_12)
  =(w_23,1),                 rho=w_12 w_23.             (JFM1)
```

The claim is that the resulting joint quotient has a homomorphism to a
finite group which is nontrivial on the head mark `w=x_13(Q)`.

## Proof correction, 2026-09-07

The former proof incorrectly placed `<F,h>` inside the marked LEF subgroup
`H=<L,a>`, where `L` is the finitary symbol kernel. The packet's tail factor
acts on infinitely many levels: its Laurent symbol is the entire constant
`EL_3(F_2)`. The constant swap `w_12` is not finitary, and `h` has a
nondiagonal symbol, whereas every element of `H` has diagonal symbol.
Thus neither `F<=L` nor `<F,h><=H` holds. In fact `<F,h>=EL_3(J)`.

The established correction
`ptfree-sep7-jacobson-packet-escapes-finitary-shift` invalidates that proof
route. No valid finite marked model for the joint quotient is supplied by
the argument. The former stronger assertion concerning every finite list
of literal relations is likewise unsupported and is not used here.

This does not refute the two-cell finite-model claim. The separate models
for individual cells and the natural-module and tail-trivial exclusions
remain available, but they do not decide the joint question. In particular,
the previous conclusion that these two cells cannot support an operator-MF
obstruction has been withdrawn.
