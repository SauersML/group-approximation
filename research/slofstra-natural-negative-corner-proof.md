---
rg: 2
id: slofstra-natural-negative-corner-proof
kind: route
title: Take the signed negative sector of Slofstra's permutation-preserving blocks
target: slofstra-natural-negative-corner-image-is-sofic
requires:
  - slofstra-involution-not-sofic-radical
  - fixed-flip-negative-corner-is-sofic
  - sofic-radical-soficization
---

The proof of `slofstra-involution-not-sofic-radical` constructs the
coordinate sign as

```text
J_n(z,e)=(z,e+1 mod 2)
```

and sends the other blocks to diagonal permutations, block swaps, and
products of those blocks. The defining centrality relations with `J_n` are
exact in the displayed construction; the exactification estimate `(FNP1)`
would suffice if one retained only their asymptotic form.

The `J_n=-1` corner is therefore invariant. Restriction to that corner keeps
every relator defect vanishing and makes `J_n=-I`. This is exactly the marked
approximate-representation input used by the linear-system perfect-strategy
dictionary, hence its limit character `chi_-` gives a perfect `C_qa`
correlation.

By `fixed-flip-negative-corner-is-sofic`, the image of this restricted
ultraproduct representation is sofic. Its kernel is precisely the ordinary
GNS kernel of `chi_-`, because a group element has character value one iff
its unitary image is the identity in normalized Hilbert--Schmidt norm.
Therefore the GNS image `(SNC2)` is isomorphic to that sofic image.
`sofic-radical-soficization` gives `(SNC3)`.
