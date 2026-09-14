---
rg: 2
id: magnus-embedding-mod-m-into-wreath-product
kind: claim
title: For F free of rank r, N normal in F and m >= 0, the Magnus map with lamps reduced modulo m has kernel [N,N]N^m, so F/[N,N]N^m embeds in (Z/m)^r wr F/N
distinct_from:
  magnus-embedding-f-over-n-prime-into-wreath-product: that is the integral Magnus embedding, with kernel [N,N]; this reduces the lamps modulo m and computes the kernel [N,N]N^m, which needs the purity of the Magnus image inside the base module.
---

**ESTABLISHED** by `magnus-embedding-mod-m-circulation-proof`. Not independently
reviewed.

## Statement

Let `F` be free on `x_1, ..., x_r`, let `N` be normal in `F`, let `G = F/N` and let
`μ : F -> G` be the quotient map. Let `T` be the free left `ZG`-module with basis
`t_1, ..., t_r`, and let `φ : F -> T ⋊ G` be the Magnus map
`x_i -> (x_i^μ, t_i)` of `magnus-embedding-f-over-n-prime-into-wreath-product`,
where `T ⋊ G ≅ Z^r wr G`.

For an integer `m >= 0` let `ρ_m : T ⋊ G -> (T/mT) ⋊ G` reduce the lamps modulo
`m`, with `Z/0 = Z`. Then `T/mT ⋊ G ≅ (Z/m)^r wr G` (restricted, regular), and

```text
ker(ρ_m ∘ φ) = [N, N] N^m .
```

So `F/[N,N]N^m` embeds in `(Z/m)^r wr F/N`.

- `m = 0` is the integral Magnus embedding.
- `m = 1` gives `ker = N`, the quotient map itself.

## Credit

A search result (Springer, *Algebra and Logic*, "Shmel'kin embeddings for abstract
and profinite groups") describes Shmel'kin's generalization of the Magnus embedding
to groups `F/V(R)` for varieties `V`. The exponent-`m` case here is presumably
contained in it. The primary sources were **not** read, so this node does not rely
on them: the route proves the statement directly from the integral Magnus embedding.
No priority is claimed.

## Consumer

`product-variety-free-groups-satisfy-permutational-boone-higman`.

_Orphan sweep (2026-09-14): this node cited `research/artifacts/bh-solvable-general-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
