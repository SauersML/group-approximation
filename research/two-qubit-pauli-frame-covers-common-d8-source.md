---
rg: 2
id: two-qubit-pauli-frame-covers-common-d8-source
kind: claim
title: The smallest two-qubit Pauli source frame collapses its forbidden selector atom
distinct_from:
  nonscalar-frame-or-selector-mixing-pays-forbidden-source: that consumes an abstract operator frame and selector-mixing rows; this constructs an explicit finite frame with `kappa=1` and wordizes its mixing residual by one existing D8 Gram row
  dihedral-spin-packet-supplies-common-partial-swap: that uses one marked two-dimensional D8 type, whose source and range are rank one and admit no proper nonscalar carrier split; this adds exactly one transverse Pauli qubit
  two-pauli-quarter-carriers-have-fixed-reflection-holonomy: that extracts a D8 holonomy from two atlas Hecke projections; this is a standalone order-thirty-two group packet with literal group-algebra carrier projections
  predicate-preserving-nonscalar-frames-miss-forbidden-source: that rules out transports preserving the allowed selector support; this deliberately prices the failure of selector equivariance by an ordinary row word
  algebraic-selector-mixing-frame-collapses-forbidden-sector: that proves the abstract zero-defect firewall for every algebraic frame; this constructs the minimal Pauli frame explicitly and computes its collapse as one four-letter word identity
---

Let `K` be the central product of two copies of `D_8`, presented by
involutions `y,z,j,a,b` with `y` central,

```text
zj=yjz,                 ab=yba,
[z,a]=[z,b]=[j,a]=[j,b]=1.                             (TPF1)
```

On the marked sector `P=(1-y)/2`, put

```text
T=P(1+z)/2,            Q=P(1-z)/2,
S=TjQ,
q_+=T(1+a)/2,          q_-=T(1-a)/2.                  (TPF2)
```

Then `S^*S=Q`, `SS^*=T`, the two target carriers are nonzero proper
orthogonal projections exchanged by the Clifford/Pauli flip `b`, and their
pullbacks form the exact common-source frame

```text
S^*q_+S+S^*q_-S=Q.                                    (TPF3)
```

Thus `(NSF4)` holds with two carriers and `kappa=1` in every marked
representation of the finite packet, including arbitrary multiplicity.

The associated selector-mixing residual is already an ordinary D8 Gram row.
Let `p<=Q` be any source allowed-support projection, set `F=Q-p`, and suppose
`d` is a self-adjoint involution commuting with `y,z` whose marked blocks are

```text
TdT=-T,                   QdQ=2p-Q.                   (TPF4)
```

Then the single word

```text
w=zjdj                                                   (TPF5)
```

satisfies the exact identity

```text
||(w-1)P||_2^2=4||SF||_2^2=4||F||_2^2.                (TPF6)
```

For both frame carriers take target allowed projection `p_i=T` and transport
`S_i=S`.  Their literal mixing residual is

```text
p_iS_i-S_ip=SF,                                        (TPF7)
```

so `(TPF6)` wordizes the entire selector-mixing payment in `(NSF5)` with no
dimension loss.  The two identical transport rows need be charged only once.

## Minimality and exact collapse

The original marked D8 type has dimension two, hence `Q` and `T` have rank
one.  It has no nonzero proper carrier inside `T`, so every one-carrier frame
there is scalar on the target range.  A nonscalar orthogonal carrier frame
requires `rank(T)>=2`; because `j` exchanges `Q` and `T`, the marked packet
must have dimension at least four.  The packet `(TPF1)` has a unique marked
spin type of dimension four and attains this bound.  Thus it is minimal among
Pauli/Weyl packets carrying a proper two-atom frame of this form.

The selected perfect predicate sector by itself is compatible with the row.
When `p=Q`, choose `d=yz`; on `P` this has blocks `-T+Q`, so `(TPF4)` holds,
and the group relations give

```text
zj(yz)j=y(zjzj)=y^2=1.                                (TPF8)
```

But this does not give phase-safe exact completeness of the **full** marked
selector packet.  If the word `(TPF5)` is imposed as a group relator, then
`(TPF6)` forces

```text
F=Q-p=0                                                   (TPF9)
```

in every representation of the quotient.  A finite marked selector packet
with a forbidden character below `Q` has `F!=0` in its group algebra, so its
embedding into the quotient collapses.  The perfect selected sector survives
only because it already has `F=0`; the unwanted companion sectors required by
phase-safe packet embedding do not.

## Sharp remaining boundary

Thus the smallest possible Weyl/Clifford frame is already on the forbidden
side of `algebraic-selector-mixing-frame-collapses-forbidden-sector`.  Making
the frame larger, replacing the transverse Pauli by a finite Weyl system, or
adding Clifford conjugates cannot help: every such fixed finite-packet frame
is still an operator identity in the full group C-star algebra and exact
mixing rows still force `(TPF9)`.

The surviving target must make the frame lower bound genuinely
finite-matrix or canonical-trace-only.  The fixed packet may still wordize
the mixing residual, but no fixed algebraic Weyl/Clifford carrier family can
supply its lower bound while the full forbidden selector packet embeds.
