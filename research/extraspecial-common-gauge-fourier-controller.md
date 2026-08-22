---
rg: 2
id: extraspecial-common-gauge-fourier-controller
kind: claim
title: An extraspecial spin packet gives a common-gauge Fourier controller
distinct_from:
  finite-cocycle-select-forces-one-common-lcu-gauge: that uses the full coordinate-lamp wreath packet for an arbitrary finite group; this replaces the exponential lamp algebra by the unique spin representation when the payload index group is an elementary abelian two-group.
  heisenberg-subgroup-cuts-are-affine-stabilizer-flats: that classifies projections cut out by Pauli subgroup characters; this uses exactly such an affine Reynolds projection and does not claim that it selects a nonlinear Boolean support.
---

**ESTABLISHED.**  Let `K=F_2^k`.  Use the extraspecial Pauli group

```text
E_k=<J,X_i,Z_i |
 J^2=X_i^2=Z_i^2=1, J central,
 [X_i,X_j]=[Z_i,Z_j]=1,
 [X_i,Z_j]=J^(delta_ij)>.                              (ESF1)
```

Let `W_1,...,W_k` be commuting payload involutions which commute with
`E_k`, and write `W_x=product_i W_i^(x_i)`.  Adjoin one unitary `C` with

```text
[C,Z_i]=1,
C X_i C^(-1) X_i^(-1)=W_i.                            (ESF2)
```

In every unitary representation on which `J=-1`, the restriction to `E_k`
is the unique `2^k`-dimensional spin representation tensored with a
multiplicity space.  In the simultaneous `Z`-eigenbasis, `(ESF2)` forces

```text
C=sum_(x in K) |x><x| tensor W_x A                    (ESF3)
```

for one common right unitary `A` on the multiplicity space.  Thus there is
no coordinate-dependent orientation gauge.

Put

```text
e_-=(1-J)/2,
q=e_- |K|^(-1) sum_(x in K) X_x,
P_K=|K|^(-1) sum_(x in K) W_x.                        (ESF4)
```

The second factor in `q` is the Reynolds projection onto the common
`X_i=+1` line of the spin packet.  Equation `(ESF3)` gives

```text
q C q = q tensor P_K A,
||qCq||_(2,q)=||P_K||_2.                              (ESF5)
```

Since the `W_i` are commuting involutions, `P_K` is exactly the projection
onto their common `+1` subspace.  Consequently

```text
qCq=0  iff  the payload K-representation has no trivial character.
                                                                  (ESF6)
```

The source projection is algebraic and has fixed canonical density

```text
tau_Gamma(q)=1/(2|K|)                                  (ESF7)
```

whenever the Pauli subgroup embeds.  The explicit spin completion below is
faithful on `E_k`, so the controller relations themselves preserve that
subgroup.

For fixed `k` the calculation is robust in normalized Hilbert--Schmidt
norm.  First round the finite Pauli packet and the finite payload `K` table.
The finite `Z`-averaging conditional expectation makes `C` block diagonal;
telescoping `(ESF2)` along the fixed hypercube then gives `(ESF3)` up to
`O_k(delta)`.  Compression by the fixed Reynolds idempotent gives `(ESF5)`
with the same dimension-independent modulus.

The common right gauge can also be absorbed by one ordinary auxiliary
unitary.  Adjoin `S` with

```text
[S,X_i]=[S,Z_i]=[S,J]=1,       (SC)^2=1.              (ESF8)
```

In the exact completion `(ESF3)`, take `S=1 tensor A^*`.  Then `SC` is the
conjugate by `A` of the diagonal involution with blocks `W_x`.  Moreover `S`
stabilizes `q`, so

```text
qSCq=S qCq.                                           (ESF9)
```

Thus the unknown common gauge is not the remaining obstruction: the
selected compression vanishes for `C` exactly when it vanishes for the
ordinary involutive payload word `SC`.

## Exact boundary

This construction does **not** yet turn `(ESF6)` into an ordinary group
relation for `k>1`, even after `(ESF8)`.  The uniform source is the joint fixed atom of all
`X_i`; it is not the spectral half of one group involution.  Killing its
compression is exactly the remaining selected-small-atom wordization
problem.  Equation `(ESF8)` supplies the stabilizer corrector, but not an
ordinary group relation whose source projection is that rank-`1/|K|` atom.

For `k=1`, the source is already a joint atom of the central sign and one
Pauli grading, so `central-marked-two-cycle-zero-compression-cell` applies
directly.  For larger `k`, replacing the joint atom by one or two Pauli cuts
would retain an affine family of characters rather than the single trivial
character.  Thus the result removes the exponential coordinate-lamp packet
and all SELECT gauge ambiguity, but it does not evade the affine-support
barrier.
