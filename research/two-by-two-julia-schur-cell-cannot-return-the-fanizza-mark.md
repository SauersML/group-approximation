---
rg: 2
id: two-by-two-julia-schur-cell-cannot-return-the-fanizza-mark
kind: claim
title: A natural two-by-two Julia or Schur cell cannot return the Fanizza mark
distinct_from:
  fixed-packet-julia-calculus-is-tracially-functorial: that proves the general regular-representation firewall; this additionally computes the exact opposite-root two-by-two commutator and shows why it does not realize the minimal additive trace-zero endpoint.
  one-additive-commutator-suffices-for-julia-return: that proves one additive commutator is semantically sufficient and gives a three-by-three Steinberg wordization; this proves the standard two-by-two elementary cell does not provide the same coefficient isolation.
  universal-block-return-violates-the-regular-firewall: that rules out a universal proper return abstractly; this identifies the precise algebraic contamination in the smallest proposed block linearization.
---

ESTABLISHED TWO-BY-TWO FENCE.  Fix one heat depth and contraction `B`.  The
standard Julia reflection on two copies exactly exposes

```text
 E Q_B E=diag(B^*B,0),                                  (TJS1)
```

but every construction from this block using fixed packet coefficients,
compression, ordinary Schur complements with an invertible pivot, polar
decomposition, and continuous functional calculus is tracially functorial.
Therefore it cannot compare a fixed positive regular carrier `P` with
`B^*B` only in finite matrices.  If the comparison were a zero-defect
consequence of the group relations, it would hold in the regular finite von
Neumann algebra at every depth and force `tr(P)=0`.

The square Schur-complement calculation already displays the missing
scalar.  For

```text
 M=[I Y;X I],
```

the two unit-pivot complements are `I-YX` and `I-XY`.  In every finite
tracial algebra

```text
 tr(I-YX)=tr(I-XY).                                    (TJS1')
```

Changing pivot orientation therefore creates no trace deficit.  A deficit
requires genuinely rectangular maps between unequal-trace carriers, which
is precisely the proper-corner datum forbidden by the regular firewall,
not something supplied by a square `2 by 2` linearization.

Nor does replacing Julia compression by the standard opposite-root
`2 by 2` elementary commutator isolate the additive trace-zero certificate
of `one-additive-commutator-suffices-for-julia-return`.  Over an arbitrary
unital coefficient algebra put

```text
 u=e_12(Y)=[I Y;0 I],          v=e_21(X)=[I 0;X I].
```

Then direct multiplication gives

```text
 [u,v]
 =[ I+YX+YXYX    -YXY ;
       XYX         I-XY ].                              (TJS2)
```

Thus no corner equals `I+[Y,X]`; the diagonal carries both `YX,XY` and the
quartic term `YXYX`, while the off-diagonal corners are cubic.  Cyclic trace
does not remove the contamination: the trace of the nonidentity diagonal
part is `tr(YXYX)`, not zero.

Consequently the natural two-by-two routes have an exact dichotomy:

1. Julia/Schur calculus retains the desired positive amplitude but is
   regular-tracially functorial and supplies no matrix-only return;
2. opposite elementary roots are group-word native but do not isolate the
   additive commutator whose trace detects `P-B^*B`.

The constant-size coefficient isolation first available from standard root
relations is the `3 by 3` Steinberg identity `(ACJ9)`.  That identity solves
wordization only after a characteristic-zero, trace-reflecting coefficient
chart has been authenticated; it does not solve the remaining Fanizza
groupification.
