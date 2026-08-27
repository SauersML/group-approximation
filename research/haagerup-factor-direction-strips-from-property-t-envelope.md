---
rg: 2
id: haagerup-factor-direction-strips-from-property-t-envelope
kind: claim
title: A Haagerup direct factor cannot carry the property-T part of a mixed algebraic envelope
distinct_from:
  haagerup-actors-cannot-host-property-t-algebraic-envelope: that excludes a Haagerup TOTAL actor over an abelian base; this allows a non-Haagerup total actor and strips only one Haagerup direct factor by intertwining into the complementary crossed product.
  nonhaagerup-spectator-must-couple-nonamenably: that proves soficity when the added spectator has amenable module image; this applies to every commuting module action, including infinite nonamenable spectator image, and uses rigidity of the embedded factor.
  coinduction-preserves-but-cannot-create-algebraic-envelope: that treats change of actor through coordinate coinduction; this treats genuinely mixed modules for a direct-product actor and makes no coordinate or Cartan assumption on the embedded factor.
---

Let `Gamma` be Haagerup, let `H` be any countable group, and let the two
groups act commuting and trace-preservingly on a finite von Neumann algebra
`B`.  Set

```text
P = B rtimes H,
M = B rtimes (Gamma x H) = P rtimes Gamma.              (HFS1)
```

Every property-`(T)` `II_1` subfactor `Q subset M` intertwines into `P` in
Popa's sense:

```text
Q prec_M P.                                             (HFS2)
```

Consequently, if `Q` is not Connes embeddable, then `P` is not Connes
embeddable.

Apply this with `Gamma=Gamma_Manzoor` (virtually free, hence Haagerup),
`H=SL_3(Z)`, `B=L^infinity(K,Haar)`, and `A=K-hat`.  For **every** compact
abelian algebraic action of `Gamma x H`, including a genuinely mixed module
with infinite nonamenable `H`-image, an embedding of the fixed property-`(T)`
non-CE factor into the total crossed product already forces

```text
L^infinity(K) rtimes SL_3(Z) = L(A rtimes SL_3(Z))
```

to be non-CE.  Thus `A rtimes SL_3(Z)` is itself non-hyperlinear.  The
Manzoor direction cannot transport the non-CE factor, even non-Cartanly; a
successful mixed module is automatically a solution after forgetting that
direction.
