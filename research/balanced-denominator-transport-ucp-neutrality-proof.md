---
rg: 2
id: balanced-denominator-transport-ucp-neutrality-proof
kind: route
title: Tensor a coprime congruence actor with an invisible denominator multiplicity twist
target: balanced-denominator-transport-is-ucp-neutral
requires:
  - one-britton-moment-forces-uniform-actor-noncorrectability
---

Reduction modulo `q` extends from `Lambda` to `Gamma`, because `p` is a
unit modulo `q`.  Hence `bar h` is defined and

```text
bar h bar s bar h^(-1)=bar s^p.                         (BDP1)
```

The tuple `g |-> X_g` in `(BDU1)` is a genuine twofold amplification of a
finite-dimensional representation of `Lambda`.  The corresponding star
homomorphism `C^*(Lambda)->M_(2|Q|)` is ucp, proving `(BDU2)`.  Since `T`
acts only on the first tensor factor, `(BDU3)` is immediate.  Direct
multiplication gives

```text
[T_0,H_0]=[[0,1],[-1,0]],
```

so its normalized trace is zero and `(BDU4)` follows.

The first tensor factor of a conjugacy word cancels:

```text
H X_s H^*
 =I_2 tensor lambda_q(bar h bar s bar h^(-1))
 =I_2 tensor lambda_q(bar s^p)
 =X_(s^p),                                               (BDP2)
```

proving `(BDU5)`.  More generally, all lattice letters act trivially on the
first tensor factor.  Therefore a word `w` evaluates there to
`H_0^e`, where `e` is its total denominator-letter exponent.  On the second
factor it is the reduction modulo `q` of the same arithmetic word.  If
`w=1` in `Gamma` and `e=0`, both factors are the identity, proving `(BDU6)`.

Finally `(BDU3)--(BDU4)` put the packet into `(BNC1)` with
`delta_C=delta_B=0`.  Applying
`one-britton-moment-forces-uniform-actor-noncorrectability` gives `(BDU7)`.
Since `(BDU2)` says the primal matrix-range distance is zero, every dual
support-function gap is nonpositive:

```text
Re sum_s tr(B_s^*X_s)-h_d(B)<=0                         (BDP3)
```

for every tuple `B`.  This proves the claimed UCP-neutrality, including for
the generator-diagonal separator.

For completeness, `Gamma` is perfect.  Over the Euclidean ring
`Z[1/p]`, `SL_3=E_3`, and each elementary generator is a commutator

```text
x_ij(a)=[x_ik(a),x_kj(1)]       (i,j,k distinct).       (BDP4)
```

Consequently total `h`-exponent cannot descend to a homomorphism
`Gamma->Z`.  Some identity consequence of a full presentation therefore
has nonzero `h`-exponent and detects the multiplicity factor `H_0`; this is
exactly the information omitted by the balanced packet.
