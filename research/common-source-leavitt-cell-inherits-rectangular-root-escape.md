---
rg: 2
id: common-source-leavitt-cell-inherits-rectangular-root-escape
kind: claim
title: A relative Leavitt common-source cell still needs one same-reservoir scalar
distinct_from:
  capacity-gated-common-source-gram-word-cell: that asks directly for common source-Gram context intertwiners in matrix microstates; this audits the proposed Leavitt--Steinberg implementation and identifies the exact decoder statement it still needs.
  affine-leavitt-boundary-shear-payment: that studies the full binary affine-Leavitt coefficient system; this gives the fixed four-context rectangular model relevant to the Fanizza common-source cell.
  rectangular-escape: that gives the two-child paired-label countermodel; this records its four-target version and explains why finitely many root Fourier tables do not decode actual partial isometries.
---

There is a formally clean additive implementation of the Fanizza
common-source cell.  In a relative coefficient star algebra, adjoin one
source projection `Q` and four context arrows `s_c` with formal reverses
`t_c`, impose

```text
t_c s_c=Q,
A_(c,x)s_c=s_c Z_x,
t_c A_(c,x)=Z_x t_c,                                   (CLR1)
```

and impose the allowed context relations on the `A_(c,x)` in the range of
`s_c`.  If `t_c=s_c^*` in an operator model, every context arrow has the
literal same source Gram

```text
s_c^*s_c=Q.                                             (CLR2)
```

Countable amplification makes `(CLR1)--(CLR2)` compatible with exact HALT
completeness: the four target carriers may all have infinite multiplicity,
and a vanishing forbidden `Q` makes the cell vacuous.

Embedding this coefficient algebra in a Steinberg presentation does **not**
yet prove `capacity-gated-common-source-gram-word-cell`.  The missing step is
still a matrix-coordinate root decoder.  Fixed root Fourier tables recover
finite label transports, not matrices `s_c,t_c` satisfying `(CLR2)` on one
finite multiplicity reservoir.

## Four-target rectangular model

Let `b:V x W -> F_2` be a nonzero finite perfect pairing and put

```text
V'=V^4,                 W'=W^4,
b'((v_c),(w_c))=sum_c b(v_c,w_c).                       (CLR3)
```

For `c=1,2,3,4`, let `R_c:V->V'` and `L_c:W->W'` be the coordinate
embeddings.  Then exactly

```text
b'(R_c v,L_d w)=delta_(c,d)b(v,w).                      (CLR4)
```

Thus every one-level diagonal inverse and crossed-zero multiplication table
seen by the root Fourier decoder is perfect.  Nevertheless the target label
space is larger:

```text
|V'|=|V|^4,             |W'|=|W|^4.                    (CLR5)
```

The model fits in one ambient matrix size.  If `N=|V|=|W|`, put the source
Weyl representation of dimension `N` in multiplicity `N^3`, and put the
target Weyl representation of dimension `N^4` with multiplicity one.  Both
have total dimension `N^4`.  Label expansion is paid for by multiplicity
contraction, while every finite table in `(CLR4)` remains exact.

Consequently a bounded list of Steinberg multiplication triangles cannot by
itself promote the recovered arrows to actual same-source partial isometries.
The rectangular escape is already present at depth one; iteration is not
needed to exhibit it.

## Minimal scalar left after the audit

Let `p_c` be the selected target Hecke projection, `U_c` the decoded context
transport, and `Q` the capacity-gated leakage projection.  The Leavitt/root
implementation closes the Fanizza cell only after proving the square
same-reservoir saturation

```text
sum_c [tau(Q)-tau(Q U_c^*p_cU_c Q)]
 =sum_c ||(1-p_c)U_cQ||_2^2
 <= K E_rel+o(1).                                      (CLR6)
```

Equation `(CLR6)` is exactly the source-Gram row of
`common-source-hnn-bridges-need-one-gram-saturation-identity`.  Once it is
known, spectral intersection and polar rounding produce four arrows with
literal common source, and the analytic two-cell proves `NCL13`.

The point of the Leavitt proposal is therefore not that it removes `(CLR6)`.
It moves `(CLR6)` into a root-boundary statement: label enlargement as in
`(CLR5)` must either return to the same multiplicity reservoir or pay a
normalized-HS boundary defect.  This is the same finite-dimensional-only
ingredient isolated in the affine-Leavitt dossier.

## Finite-packet and exact-witness audit

- Replacing the root decoder by four finite HNN edges does not help.
  `isotypic-finite-edge-forces-full-commuting-selector-support` shows that a
  logical-invariant finite edge with zero-loss saturation has full selector
  support in its selected type.
- The exact infinite witness is not obstructed: infinite multiplicity absorbs
  the four copies and need not carry a finite normalized trace on the
  coefficient actuator.
- Any proof of `(CLR6)` by a universal tracial rank identity is invalid.  The
  payment must use finite matrix multiplicity/root coordinates; otherwise it
  would also hit the properly infinite exact witness or the non-CE regular
  model.

Thus the relative-Leavitt construction is a valid syntax for the common
source, but not yet its normalized-HS decoder.  The unique remaining scalar
is `(CLR6)`, or an equivalent fixed-depth boundary-payment inequality.
