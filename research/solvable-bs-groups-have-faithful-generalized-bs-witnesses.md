---
rg: 2
id: solvable-bs-groups-have-faithful-generalized-bs-witnesses
kind: claim
title: For |m| >= 2 the solvable Baumslag--Solitar group BS(1,m) has a faithful generalised Baumslag--Solitar witness, so every group in BS_{BS(1,m)} embeds in a simple group of type F_infinity
distinct_from:
  surface-groups-have-faithful-generalized-bs-witnesses: that supplies witnesses for surface groups by quaternion lattices; this supplies them for BS(1,m) by an index-changing HNN extension.
  faithful-generalized-bs-witnesses-pass-to-direct-products: that is the product permanence of witnesses; this adds BS(1,m) to the list of factors it can be applied to.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that is BLIW for graphs of groups over Z (BS_Z) and over F_k; this is graphs of groups over BS(1,m), whose vertex groups are not virtually abelian or free.
  ascending-hnn-of-free-groups-satisfy-boone-higman: that embeds mapping tori of free group endomorphisms in BS_{F_2}; this is the class BS_{BS(1,m)}.
---

**ESTABLISHED** through `solvable-bs-faithful-witness-proof`. Lane proof (bh-free-05),
elementary apart from BLIW Theorem 11.1. Not reviewed. No priority claimed.

## Statement

Let `|m| >= 2` and `G = BS(1,m) = < a, s | s^-1 a s = a^m > = Z[1/m] ⋊ <s>`. Choose primes
`p ≠ q` not dividing `m`, and let

    W = < a, s, t | s^-1 a s = a^m,  t a^p t^-1 = a^q,  t s t^-1 = s >,

the HNN extension of `G` along `ψ : C = <a^p, s> -> C' = <a^q, s>`, with `a^p ↦ a^q` and
`s ↦ s`. Then:
1. `C` and `C'` have index `p` and `q` in `G`, and `ψ` is an isomorphism. So `W ∈ BS_G`, the
   class of Bux--Llosa Isenrich--Wu.
2. `W` acts faithfully on its Bass--Serre tree.
3. Consequently, by BLIW Theorem 11.1 (imported verbatim in
   `bliw-locally-finite-tree-actions-embed-in-fp-simple-groups`), every group in `BS_G` embeds
   in a simple group of type `F_∞`. Here `G` is of type `F_∞`, having a finite 2-dimensional
   `K(G,1)`.
4. With `faithful-generalized-bs-witnesses-pass-to-direct-products` the same holds for `BS_P`,
   where `P` is any finite direct product of groups commensurable with `BS(1,m)`s, `Z^k`s,
   `F_k`s and closed hyperbolic surface groups.

## Examples

- `W` itself. It is non-residually-finite, since it contains `BS(p,q) = <a, t>`, and it contains
  `BS(1,m)`. It is neither linear nor hyperbolic.
- Amalgams `BS(1,m) *_C BS(1,m)` along finite-index subgroups identified by arbitrary
  isomorphisms, and HNN extensions of `BS(1,m)` along arbitrary isomorphisms of finite-index
  subgroups.
