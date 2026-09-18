---
rg: 2
id: mapping-torus-mf-radical-descends-through-kernel-radical
kind: claim
title: The MF radical of a mapping torus is pulled back from the mapping torus of the kernel's universal MF quotient
distinct_from:
  mapping-torus-mf-radical-lies-in-finite-residual: That bounds the radical above by the finite residual of the kernel; this bounds it below by the kernel's own MF radical and computes it exactly as a pullback from the MF quotient's mapping torus.
  finite-outer-order-mapping-torus-is-virtually-product: That shows a finite-order outer action gives a virtually direct product; this combines it with the descent to compute the radical exactly as the kernel's radical in that case.
  universal-mf-quotient: That constructs the universal MF quotient of one group; this transports it through an automorphism mapping torus.
  split-cyclic-kazhdan-defect-exact-mf-radical: That is the positive assembly criterion; this is the exact reduction showing that every extrinsic contribution lives in the mapping torus of an MF group.
---

Let `K` be a countable group, `phi in Aut(K)`, and

```text
G = K semidirectProduct_phi Z.
```

Put `R = Rad_MF(K)`, `Q = K/R` and let `psi` be the automorphism of `Q`
induced by `phi`.  Then:

```text
(MD1)  R is characteristic in K, so psi exists and
       G/(R x {0}) ~= Q semidirectProduct_psi Z;
(MD2)  R x {0} <= Rad_MF(G) <= K x {0};
(MD3)  Rad_MF(G) = pi^{-1}( Rad_MF(Q semidirectProduct_psi Z) ),
       where pi : G -> Q semidirectProduct_psi Z is the quotient map;
(MD4)  Rad_MF(G) = K x {0}  iff  Rad_MF(Q semidirectProduct_psi Z) = Q x {0};
(MD5)  if [phi] has finite order in Out(K), then Rad_MF(G) = R x {0}.
```

Here `Q` is MF by `universal-mf-quotient`.  So the whole extrinsic part of a
mapping-torus MF radical, meaning the part not already in the kernel's own
radical, is produced by the mapping torus of an **MF** group.

**Consequence for the torsion-free exact-radical goal.**  Let `(G,K)` be a
witness of `torsion-free-sofic-exact-mf-radical-over-z`, written as a split
mapping torus.  Then exactly one of the following holds.

```text
(DI)  Rad_MF(K) = K: the kernel is intrinsically full-radical;
(DX)  Q = K/Rad_MF(K) is a nontrivial MF group with property (T) and no
      nontrivial finite quotient, [psi] has infinite order in Out(Q), and
      Rad_MF(Q semidirectProduct_psi Z) = Q x {0}.
```

In case `(DI)` the automorphism plays no role in the radical: for every
automorphism the radical is `K`.  So a genuinely extrinsic witness exists only
if some nontrivial MF Kazhdan group without finite quotients has an
automorphism whose mapping torus has exact radical `Q`.  That is the separate
problem `mf-kazhdan-quotientless-mapping-torus-exact-radical`.  It involves
neither soficity nor torsion-freeness.  If it is false, the extrinsic route
`torsion-free-sofic-exact-mf-radical-via-extrinsic-kernel` gives nothing beyond
intrinsically full-radical kernels.

A further forced property: in any compression configuration with a Kazhdan
source `L` inside `G`, the image of `L` in `G/K ~= Z` is a Kazhdan subgroup of
`Z`, hence trivial, so `L <= K x {0}`.  Only the compressing element `t` and
the root `c` can carry a nonzero `Z`-degree.
