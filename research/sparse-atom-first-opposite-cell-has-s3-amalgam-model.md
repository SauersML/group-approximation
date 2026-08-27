---
rg: 2
id: sparse-atom-first-opposite-cell-has-s3-amalgam-model
kind: claim
title: The first opposite-root cell returns two branches to a sparse atom but has an exact S3 amalgam model
artifacts:
  - research/sparse-atom-first-opposite-cell-s3-proof.md
distinct_from:
  sparse-parabolic-atom-has-split-inertia: that computes the split inertia and never leaves the parabolic normalizer; this adjoins a genuine opposite-root A1 cell and computes its two returns on the selected rank-one character atom.
  binary-leavitt-finite-actor-minimal-atom-dichotomy: that gives monomial models for finite normalizer packets; this amalgamates such a packet with an opposite-root S3 cell and keeps a prescribed joint atom rank one.
  scalar-active-mixed-shell-has-marked-regular-model: that uses the regular representation of the whole finite scalar shell; this computes the compression geometry on one prescribed sparse atom and exhibits maximal range collision after two returns.
  common-opposite-mark-attachment-preserves-full-q-zero-type: that attaches the full common-opposite Morita table to a signed Hecke packet through the mark; this is the minimal opposite A1 attachment to an arbitrary finite character packet and records its rank-one source overlaps explicitly.
---

**ESTABLISHED FIRST-OPPOSITE-CELL FENCE.**  Let `A` be a nonzero finite
elementary abelian `2`-group, let a finite group `K` act on `A`, and choose
`0!=a_0 in A`.  On

```text
H_A=ell^2(A^)
```

use the exact diagonal--permutation representation of `A semidirect K`.
Fix a character `chi` with `chi(a_0)=-1`, and let

```text
P=|delta_chi><delta_chi|.                              (SOF1)
```

Write `u` for the represented involution `a_0`.  Adjoin an abstract
opposite-root involution `v` with the complete scalar active `A_1` table

```text
u^2=v^2=1,                 uvu=vuv,                    (SOF2)
```

so `<u,v>~=S_3`.  There is an exact finite-dimensional representation of

```text
(A semidirect K) *_(<a_0>=<u>) S_3                    (SOF3)
```

which retains the original `A semidirect K` packet and for which `P` is
still a rank-one joint `A`-character atom.

On the two-dimensional summand containing `P`, put

```text
u=[[-1,0],[0,1]],
v=[[1/2,-sqrt(3)/2],[-sqrt(3)/2,-1/2]],
w=uvu.                                                 (SOF4)
```

Set

```text
Q=vPv,                         R=wPw.                  (SOF5)
```

Then the two literal opposite-cell branches return exactly to the same
nonzero sparse atom:

```text
vQv=P,                         wRw=P.                  (SOF6)
```

Nevertheless they do not give two orthogonal copies.  Directly,

```text
PQP=PRP=(1/4)P,
||QR||_op=1/2,
Q+R=diag(1/2,3/2)             on the SOF4 block.       (SOF7)
```

Equivalently, the two return partial isometries have the identical range
`P`; their range cross-Gram has norm one.  The stabilizer of `P` inside this
`S_3` cell is `<u>`, so every exact same-atom word in the cell compresses to
the scalar `+1` or `-1`.

For the literal binary-Leavitt root shell, take

```text
u=x_ij(q),                  v=x_ji(q),
q=s_1t_1.                                               (SOF8)
```

The scalar idempotent-corner embedding

```text
M |-> I+(M-I)q
```

identifies `(SOF2)` with the ordinary opposite-root `GL_2(F_2)=S_3` cell.
Thus the first genuine opposite-root occurrence leaving the split
parabolic, even together with both of its exact returns to a prescribed
rank-one atom, supplies neither an orthogonal branch pair nor a completeness
row on that atom.

This fences precisely a finite parabolic character packet joined to one
opposite `A_1` cell only through the marked involution.  It does not model
additional Steinberg relations coupling `v` to another named parabolic
coefficient or actor occurrence.  Any live sparse-atom fold must include
such an additional mixed occurrence (or a longer word using unequal
opposite-root channels); merely exiting through the opposite root and
returning two conjugate atoms is insufficient.

No Property `(T)`, trace-density hypothesis, stability theorem, computation,
or literature input is used.

DERIVATION
sparse-atom-first-opposite-cell-s3-proof
