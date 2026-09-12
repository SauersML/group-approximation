---
rg: 2
id: dyadic-invariant-cocycle-has-a-stable-heisenberg-sign
kind: claim
title: The invariant dyadic Clifford cocycle has a stable Heisenberg sign
distinct_from:
  fixed-clifford-projective-dyadic-tower: that identifies the full twisted inertia category but does not determine whether its multiplier splits or how it behaves on commuting root pairs.
  fixed-clifford-sectors-have-zero-adjacent-opposite-overlap: that proves zero adjacent overlap by pulling back newest-layer characters and explicitly does not use the projective multipliers.
  iwahori-dual-inclusion-graph-is-fusion-not-the-bruhat-tits-tree: that identifies the one-sided fusion operator and its norm-three sectors; this computes a central-extension invariant inside one such sector.
---

Let

```text
G_a=SL_2(Z/2^a),
L_a=ker(G_a->G_(a-1)),
chi_a(1+2^(a-1)X(A,B,C))=(-1)^(A+B+C),
```

and let `omega_a` be the invariant-character multiplier from
`fixed-clifford-projective-dyadic-tower`.  The central pushout

```text
1 -> <z> ~= C_2 -> E_a:=G_a/ker(chi_a) -> G_(a-1) -> 1              (DHS1)
```

is nonsplit for every `a>=2`; in particular `omega_a` is nontrivial.

For every `a>=3` and every `r,s>=1` with `r+s=a-1`, the commuting pair in
`G_(a-1)` represented by

```text
u(2^r)=[[1,2^r],[0,1]],       l(2^s)=[[1,0],[2^s,1]]               (DHS2)
```

has lifts to `E_a` satisfying

```text
[u(2^r),l(2^s)]=z.                                                (DHS3)
```

Consequently every `omega_a`-projective representation in the fixed
Clifford sector turns this commuting pair into an anticommuting pair and
has even dimension.

This sign is stable under the anisotropic Nielsen valuation shift: wherever
both root elements remain integral, `(r,s)` is sent to `(r+1,s-1)`, and
the right side of `(DHS3)` remains `z`.  Moreover `omega_a` is
`C_2`-valued, so inversion does not produce an opposite sign.  Thus this
local Schur-multiplier invariant cannot by itself force upper/opposite
boundary: it imposes the same absorbable parity charge on both sides.
Any uniform obstruction must compare more of the projective inertia data
than this stable alternating sign.

