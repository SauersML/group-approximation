---
rg: 2
id: balanced-denominator-transport-is-ucp-neutral
kind: claim
title: Balanced denominator transport is UCP-neutral on uniform actor-outlier packets
artifacts:
  - research/balanced-denominator-transport-ucp-neutrality-proof.md
distinct_from:
  p-congruence-packet-is-ucp-exact-but-actor-nonextendable: that packet makes the denominator actor commute with the mod-p root and therefore violates the displayed root transport macroscopically; this packet uses a quotient of modulus coprime to p, satisfies the root transport and every denominator-balanced arithmetic relation exactly, and isolates the genuinely missing unbalanced closure relation.
  denominator-transport-only-conjugates-p3-multiplicity-reservoirs: that analyzes spatial gauges on decoded adjacent-depth packet factors; this is a finite exact UCP counterpacket showing directly that balanced denominator words cannot see a multiplicity twist at all.
  sl3-large-prime-hnn-matrix-range-capture: that uses every relation and canonical moment of the full arithmetic centralizer HNN group; this only fences proofs using balanced denominator-conjugacy relations together with the already established actor-outlier modulus.
---

Fix a prime `p`, put

```text
Lambda=SL_3(Z),       Gamma=SL_3(Z[1/p]),
h=diag(p,1,p^(-1)),   s=e_12(1),
```

and let `S` be a finite symmetric Kazhdan generating set of `Lambda`
containing `s`.  Choose any integer `q>=2` coprime to `p`, put
`Q=SL_3(Z/qZ)`, and let `lambda_q` be its left regular representation.
Writing `bar h=diag(p,1,p^(-1) mod q)`, there is a packet

```text
X_g=I_2 tensor lambda_q(bar g)       (g in Lambda),
H=H_0 tensor lambda_q(bar h),
T=T_0 tensor I,

T_0=diag(1,-1),
H_0=2^(-1/2) [[1,-1],[1,1]].                           (BDU1)
```

It has all of the following properties.

```text
dist_(2,S)(X,MR(Lambda,S))=0,                           (BDU2)
max_(g in S)||[T,X_g]-I||_2=0,                          (BDU3)
tr([T,H])=0,                                             (BDU4)
H X_s H^*=X_(s^p).                                      (BDU5)
```

In fact, if `w` is any word in elements of `Lambda` and `h^(plusOrMinus1)`
which is trivial in `Gamma` and whose total `h`-exponent is zero, then

```text
ev_(X,H)(w)=I.                                           (BDU6)
```

Nevertheless its distance on `S union {h}` from every same-dimensional
exact representation of `Gamma` is at least

```text
c_*=sqrt(2)/(2+4sqrt(|S|)/kappa)>0,                     (BDU7)
```

where `kappa` is a Kazhdan constant for `(Lambda,S)`.

Thus the root denominator relation -- even all denominator-balanced
arithmetic relations at once -- is exactly compatible with both a uniform
one-Britton actor outlier and **zero** lattice UCP matrix-range gap.  No
finite-window inequality can turn just those data into positive payment by
a central matrix-range separator.

This does not refute full HNN matrix-range capture.  The arithmetic group
`Gamma` is perfect, so some consequence of any presentation has nonzero
total `h`-exponent and kills the free multiplicity twist in `(BDU1)`.  A
positive proof must use such an unbalanced closure consequence (or an
equivalent simultaneous full-actor constraint), rather than only root
conjugacy.
