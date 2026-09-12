---
rg: 2
id: haagerup-targets-carry-no-relative-wall
kind: claim
title: No homomorphism of an infranormal Kazhdan pair into a Haagerup finite von Neumann algebra carries a relative wall
invalidates: [kt-ce-stabilizer-from-haagerup-target]
distinct_from:
  half-space-tail-no-go: that kills half-space tensor towers through tail triviality and a centralized-subgroup hypothesis; this kills every target with the Haagerup property, with no tensor structure and no hypothesis on what the compressor centralizes.
  kt-centralizer-normalization-hs: that is the open normalization question for tracial matrix ultraproducts, which contain property (T) algebras; this settles normalization for all Haagerup targets and says nothing about ultraproducts.
  rigid-compression-defect-normalization-dichotomy: that equates normalization in an approximation class with triviality of rigid defects; this proves normalization outright for one concrete class of targets.
---

**ESTABLISHED.** Let `Lambda <= G` be countable groups with `Lambda` having
property (T) and infranormal in `G`, i.e. the compressor semigroup
`P_Lambda = {g : g Lambda g^(-1) <= Lambda}` generates `G`. Let `(M,tau)` be a
finite von Neumann algebra with faithful normal tracial state and let
`sigma : G -> U(M)` be a homomorphism such that `sigma(Lambda)''` has the
Haagerup property (for example `M` amenable, or `M` with separable predual and
the Haagerup property). Then

```text
Ad sigma(g)(M cap sigma(Lambda)') = M cap sigma(Lambda)'     for every g in G.     (HNW1)
```

If moreover `Lambda` is not normal in `G`, then no countable family
`(x_i) subset M` has common commutation stabilizer
`{g in G : [sigma(g), x_i] = 0 for all i}` equal to `Lambda`.

So Haagerup targets — hyperfinite algebras, free group factors, amalgamated
free products over amenable subalgebras, crossed products of amenable algebras
by amenable groups — can neither host a relative wall nor witness relative
embeddability of an infranormal non-normal Kazhdan subgroup through
`ce-stabilizer-criterion-needs-no-trace`.

DERIVATION
haagerup-no-wall-proof
