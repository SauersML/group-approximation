---
rg: 2
id: rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group
kind: claim
title: A residually finite hyperbolic group containing an infranormal non-normal Kazhdan pair yields a nonsofic group with unique products
distinct_from:
  hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup: that exhibits a rigid pair inside one hyperbolic Kazhdan group whose residual finiteness is open; this converts residual finiteness of any hyperbolic host of a rigid pair into a nonsofic group with unique products.
  left-orderable-group-with-rigid-compression-pair: that is the input of the left-orderable integer-lamp construction, gated by Navas's Question 3; this is the unique-product version of the construction, gated instead by residual finiteness of a hyperbolic host, where property (T) is no obstacle.
---

**ESTABLISHED.**  Let `G` be a word-hyperbolic group and `Gamma <= E <= G` with
`Gamma` and `E` Kazhdan, `Gamma` infranormal and not normal in `E`.  Suppose
`G` is residually finite.  Then there is a normal subgroup `G_k` of finite index
in `G` such that, with `Gamma_k = Gamma cap G_k` and `E_k = E cap G_k`:

1. `G_k` has unique products, and in particular is torsion-free;
2. `Gamma_k <= E_k` are Kazhdan, and `Gamma_k` is infranormal and not normal
   in `E_k`;
3. `W = (direct_sum_(E_k/Gamma_k) Z) x| E_k` has unique products and is not
   sofic.

**Consequences for Kaplansky's conjectures.**  For every field `K`, the group
ring `K[W]` has no zero divisors and only trivial units, by the unique product
property.  So it is directly finite.  If the hypothesis holds, then some
torsion-free nonsofic group satisfies the unit and zero-divisor conjectures.
Direct finiteness alone is already known for some nonsofic groups: the
Kun--Thom binary wreaths are stably finite over every field
(`kun-thom-wreath-stably-finite`).  Those groups have torsion, though.  No
nonsofic group satisfying the unit or zero-divisor conjecture is recorded in
this graph.

**Instance.**  The hyperbolic Kazhdan cover of the binary Leavitt unit group
carries such a pair (`hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`).
So its residual finiteness would give a unique-product nonsofic group.  See
`non-rf-hyperbolic-group-or-unique-product-nonsofic-group`.

Derivation: `rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group-proof`.
