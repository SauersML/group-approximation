---
rg: 2
id: binary-jacobson-joint-shortest-cells-exclude-natural-completions
kind: claim
title: The two shortest Jacobson cells exclude every natural head-factor completion
distinct_from:
  binary-jacobson-first-mixed-kernel-is-three-syllable: that retains the mark after imposing only the controlled-swap cell by retracting to the finite packet; this proves that no natural head-module completion of that retraction can also satisfy the affine braid.
  binary-jacobson-shortest-affine-braid-is-finite-marked: that gives a finite marked quotient after imposing only the affine braid and computes the residual failure of the controlled-swap cell in dimension four; this proves the same residual transverse swap is forced in every auxiliary dimension.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks for a dimension-independent operator-norm common return in arbitrary matrix models; this is an exact finite-field obstruction for the natural head-factor family and does not classify arbitrary complex representations.
---

**ESTABLISHED.**  Retain

```text
F=G_Q x G_P,             G_Q=G_P=GL_3(F_2),
K={(g,1):g acts on <e_1,e_3> and fixes e_2},
Gamma_F=F *_K (K x <h>)
```

from `binary-jacobson-one-step-finite-type-envelope-is-marked-mf`.  Let
`u=w_12`, `s=w_23`, and let `r=w_123` be the constant three-cycle.  Consider
the quotient of `Gamma_F` by both shortest cells:

```text
(h s)^3=1,                                                   (JJC1)

(r^2 h u r^(-2))(r h u r^(-1))(h u)=c,                     (JJC2)
```

where `c=(s,1) in G_Q x G_P` is the head-controlled swap.

There is no homomorphism from this joint quotient to any `GL(V,F_2)` of the
following natural marked form.  Namely, it is impossible that

* the vertex group `F` acts through its projection to `G_Q`;
* `G_Q` acts naturally on a three-dimensional summand
  `H=<e_1,e_2,e_3>` and trivially on an arbitrary finite-dimensional
  spectator `A`; and
* the image of `h` is any involution compatible with the overlap `K`.

This is uniform in `dim(A)`.  The braid itself forces a nonzero spectator
vector `t` and the exact swap

```text
h|_<e_1,e_2,e_3,t> = (e_2 t).                             (JJC3)
```

On that invariant four-space, the left side of `(JJC2)` is then

```text
(e_1 t)(e_2 e_3),                                         (JJC4)
```

whereas its right side is `(e_2 e_3)`.  The uncancelled transverse swap
`(e_1 t)` makes equality impossible.

Thus the failure `w_14` found in the four-dimensional affine-braid model is
not an artifact of choosing one spectator coordinate: it is forced by the
two cell relations in every natural head-plus-spectator completion.  This is
a genuine joint-holonomy obstruction and shows that the two shortest cells
cannot be absorbed by merely enlarging the natural `F_2` module.

The statement is intentionally not promoted to arbitrary unitary packets.
A finite marked countermodel, if one exists, must use a nonnatural complex
`GL_3(2)` type or retain a nontrivial tail-factor action which mixes the two
cell holonomies.  Conversely, a full PI proof still needs to rule out those
possibilities with occurrence-authenticated operator-norm estimates.

DERIVATION
binary-jacobson-joint-natural-completion-proof
