---
rg: 2
id: extendable-edge-hnn-embeds-in-identity-hnn-of-mapping-torus
kind: claim
title: An HNN extension whose edge map extends to an automorphism of an overgroup embeds in an identity-edge HNN extension of the mapping torus
distinct_from:
  bh-embeddability-survives-decidable-edge-hnn: that is the open permanence for arbitrary edge maps; this is an embedding lemma that splits the extendable case of it into a mapping-torus step and an identity-edge step, and records invariants where the extension step fails over free overgroups.
  stable-permutation-hnn-of-type-a-actor-is-type-a: that realizes the stable letter by a permutation normalizing a type (A) actor; this realizes it as a product u s of an automorphism letter and a letter centralizing the edge, inside an abstract group, with no action.
  mif-free-product-automorphism-ascending-hnn-is-pbh: that treats HNN extensions along a full automorphism of M * F_m; this reduces HNN extensions along a partial isomorphism that extends to such an automorphism to that full case plus an identity edge.
  finite-index-edge-hnn-embeds-in-fp-simple-group: that handles finite-index edges through tree hosts; this handles possibly infinite-index edges and uses no host.
---

**ESTABLISHED** through `extendable-edge-hnn-untwisting-proof`. Elementary
(Britton's lemma); not independently reviewed.

## Statement

**(i) Untwisting.** Let `A <= A'` be groups, `Phi in Aut(A')`, and `C <= A` a
subgroup with `D := Phi(C) <= A`. Put `phi = Phi|_C : C -> D`. Then

```text
A*_phi = < A, t | t c t^-1 = phi(c), c in C >
```

embeds in

```text
H = (A' ⋊_Phi Z) *_{id_C} = < A', u, s | u x u^-1 = Phi(x) (x in A'), s c s^-1 = c (c in C) >
    = (A' ⋊_Phi Z) *_C (C × Z),
```

by `a |-> a` and `t |-> u s`.

**(ii) Clean free-base inputs extend inside the base.** If `F` is free of finite
rank and `C, D` are free factors of `F` with an isomorphism `phi : C -> D`, then
`phi` is the restriction of some `Phi in Aut(F)`. So (i) applies with `A = A' = F`,
and `F*_phi <= (F ⋊_Phi Z) *_C (C × Z)`.

**(iii) Where extension over a free overgroup fails.** Let `C <= F`, with `F` free,
and `phi : C -> D <= F` an isomorphism. No free group `F' >= F` carries an
automorphism restricting to `phi` if either of these holds:
- **root exponent:** some `1 != c in C` has `phi(c)^m` conjugate in `F` to `c^n`
  with `|m| != |n|`;
- **lower central depth:** some `1 != c in C` has `phi(c) in [N_c, F]`, where
  `N_c` is the normal closure of `c` in `F`. For example `phi(a) = [a, b]` in
  `F = <a, b>`, `C = <a>`.

The invariants are the maximal root exponent `e(x) = max{k : x = y^k}` and the
depth `d(x) = max{k : x in gamma_k(F')}`. Both are unchanged by automorphisms of
`F'`.

## Consequence for the permanence problem

For an input `(A, C, phi)` of `bh-embeddability-survives-decidable-edge-hnn`
admitting an extension `(A', Phi)`, the conclusion follows from two
prerequisites, which can fail separately:
- **(P1) mapping torus:** `A' ⋊_Phi Z` embeds in a finitely presented simple group
  (or lies in `B_A`);
- **(P2) identity edge:** `G *_C (C × Z)` embeds in a finitely presented simple
  group, for `G = A' ⋊_Phi Z` and this `C`.

(P1) is known for:
- `A'` free of finite rank (`virtually-free-by-cyclic-groups-satisfy-boone-higman`);
- `A'` finitely presented simple MIF (`outer-extensions-of-fp-simple-mif-groups-satisfy-pbh`);
- `A' = M * F_m` with `M` finitely presented simple MIF
  (`mif-free-product-automorphism-ascending-hnn-is-pbh`).

(P2) is the identity-map case of the permanence problem over the base `G`, and it
is open. It still carries the undecidability of
`bh-embeddability-forces-decidable-edge-membership`, whose witness is an
identity edge. So this lemma moves every twist into a mapping torus, where the
known theorems live, and leaves only an untwisted edge. It does not reduce the
difficulty of the untwisted edge.

Over free overgroups, (iii) shows the twist cannot always be absorbed:
- every input hit by the root-exponent obstruction is unbalanced: `t c t^-1 = phi(c)`
  makes `c^m` conjugate to `c^n` in `F*_phi`, with `|m| != |n|`;
- the depth obstruction also hits balanced cyclic-edge inputs such as
  `< a, b, t | t a t^-1 = [a, b] >`.
