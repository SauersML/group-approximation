---
rg: 2
id: atlas-m2-escape-kills-collision-only-scalars
kind: claim
title: The multiplicity-two escape kills every collision-only Atlas scalar ceiling
distinct_from:
  atlas-multiplicity-two-packet-collision-hub-escape: that constructs and verifies the literal GL8(2) witness; this evaluates the surviving scalar trace, Dirichlet, and ellipse frontiers on its finite regular representation.
  atlas-q14-augmented-zero-set-has-x30-one-escape: that is an exact finite-factor fence for the stronger augmented system; this is a finite-dimensional refutation of claims which assume only packet and collision.
---

Pass the exact multiplicity-two packet-and-collision witness to the regular
representation of its finite generated group, as in
`atlas-multiplicity-two-packet-collision-hub-escape`.  Packet defect and
collision defect are zero.  For the hub `b=t23`, however,

```text
V(b)=lambda(h),               ord(h)=4.
```

The canonical trace of a nonidentity element in a finite regular
representation is zero.  Therefore

```text
Re tau(V(t23))=0,
1-Re tau(V(t23))=1,
||V(t23)-1||_2^2=2.                               (M2S1)
```

It follows immediately that:

1. the hub readout `(A4-TRACE-2)` has left side `1` and right side `0`;
2. the four-cycle Dirichlet energy satisfies `E_T>=1` at zero joint residual;
3. in root-energy coordinates `x_23=1`, hence `S>=2` and

   ```text
   F=S^2+S x_12+x_12^2>=4.                         (M2S2)
   ```

Thus the collision-only four-cycle trace compiler, four-cycle Dirichlet
compiler, `1/1536` Dirichlet ceiling, and `3/128` root ellipse ceiling are all
false in one exact finite-dimensional regular-margin model.

This witness has nontrivial q14 and therefore does not refute the augmented
packet-plus-collision-plus-q14 matrix lane.  On that lane, however,
`atlas-q14-augmented-zero-set-has-x30-one-escape` supplies an exact finite
tracial factor point with `x_30^2=1`.  Consequently q14 cannot rescue any
**universal tracial** Gram/SOS upper ceiling; the only surviving possibility
is a genuinely matrix/Connes-embedding-sensitive positive residual gap for
the augmented system.

