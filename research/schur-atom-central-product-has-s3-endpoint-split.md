---
rg: 2
id: schur-atom-central-product-has-s3-endpoint-split
kind: claim
title: Central-producting a Schur forbidden atom with the S3 packet gives its exact active-exit endpoint split
distinct_from:
  mixed-central-router-adjoins-without-collapsing-packet: that amalgamates a four-generator CNOT router over a relative Pauli pair; this central-products the six-generator S3 endpoint packet only over the two central signs and makes the whole S3 packet commute with the Schur selector algebra.
  s3-active-complement-is-three-equal-scale-affine-atoms: that computes the four endpoint scales inside the S3 packet; this identifies its jump sign with the literal Schur forbidden-atom commutator and proves the compressed active/exit balance.
---

Fix a forbidden selector atom `p_a` of a Schur--Clifford predicate packet.
Let `P_a,Q_a` be its corrected relative Pauli words, put

```text
K=[P_a,Q_a],
```

and retain the marked central sign `J`.  Take the six-generator S3 packet with
central signs also named `J,K`, and form the central product over `<J,K>`:
the two packet factors commute and their copies of `J,K` are identified.
Both packet factors embed.

Let `b` be any nonzero S3 endpoint word and put

```text
Q=(1-J)/2,       F=(1-K)/2,       B=(1-b)/2,
X_a=p_a Q F B,   A_a=p_a Q-X_a.                        (SCP1)
```

Then, in every exact finite-dimensional representation,

```text
tau(X_a)=tau(p_a Q)/2,
tau(A_a)=tau(p_a Q)/2,                                 (SCP2)
```

on the forbidden atom, while every `K=+1` endpoint character belongs to the
active complement and none is charged to `X_a`.  More invariantly, measured
in the common four-dimensional S3 spin unit,

```text
two Schur child copies = one active copy + one exit copy. (SCP3)
```

The endpoint involutions commute with the entire Schur packet, and therefore
with all retained shared BCS words.  The construction is finite, effective,
and preserves every exact marked representation after amplification.

After flexible exactification of the two fixed finite packet factors and
alignment over `<J,K>`, `(SCP1)--(SCP3)` hold up to a fixed multiple of
`sqrt(E)`, independent of matrix dimension.

