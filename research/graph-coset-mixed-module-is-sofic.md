---
rg: 2
id: graph-coset-mixed-module-is-sofic
kind: claim
title: Graph-coset coupling of the replacement actor gives a sofic wreath group
distinct_from:
  nonhaagerup-spectator-must-couple-nonamenably: that forces the new non-Haagerup direction to act nonamenably on the module; this shows that the simplest genuinely mixed infinite-image coset module is nevertheless sofic.
  coinduction-preserves-but-cannot-create-algebraic-envelope: that rules out the canonical probability corner at infinite index; this proves positive soficity of a mixed coset action by subgroup separability.
  coordinate-action-not-sofic: that uses a deliberately nonseparable arithmetic stabilizer; this explains why graph stabilizers in a direct-product replacement actor cannot reproduce that phenomenon.
---

Let `Gamma` and `H` be sofic groups, assume `H` is residually finite, and
let `phi:Gamma -> H` be any homomorphism.  In

```text
Lambda = Gamma x H,
L_phi = {(g,phi(g)) : g in Gamma},
```

the graph subgroup `L_phi` is separable.  Hence the transitive action
`Lambda curvearrowright Lambda/L_phi` has exact finite Schreier
approximations and is sofic.  For every finite lamp group `F`, the generalized
wreath product

```text
(direct_sum_(Lambda/L_phi) F) rtimes Lambda              (GCM1)
```

is sofic.

More generally, assume `Gamma` is LERF and let `L<Gamma x H` be finitely
generated with injective projection to `Gamma`.  Then `L` is the graph of a
homomorphism `phi:P->H` over the finitely generated subgroup
`P=pr_Gamma(L)`, and `L` is separable in `Gamma x H`.  Its coset action and
every finite-lamp generalized wreath product over it are therefore sofic.

Applied to `Gamma=Gamma_Manzoor` and `H=SL_3(Z)`, this rules out the most
obvious mixed module for the explicit actor of
`nonhaagerup-spectator-must-couple-nonamenably`.  Even when the `SL_3(Z)`
direction has infinite nonamenable image on the coset module, graph coupling
cannot carry the fixed non-CE envelope.  A surviving mixed construction must
use a nonseparable stabilizer (as the Kun--Thom mechanism does) or a genuinely
non-permutation module.  Since `Gamma_Manzoor` is virtually free and hence
LERF, any finitely generated nonseparable stabilizer in the direct-product
actor must in addition have nontrivial intersection with the vertical
`SL_3(Z)` factor; otherwise its projection is injective and the preceding
theorem separates it.  The only alternative is an infinitely generated
stabilizer.
