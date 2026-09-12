---
rg: 2
id: injective-ca-product-trace-zero-one-law-proof
kind: route
title: Push a Garden of Eden to infinitely many disjoint windows and read the product trace
target: injective-ca-product-trace-zero-one-law
requires:
  - bijective-ca-preserve-uniform-bernoulli-measure
artifacts:
  - research/artifacts/gottschalk-product-trace-zero-one-law-2026-09-12.md
  - research/artifacts/gottschalk-quantum-compression-2026-09-07.md
---

Section 3 of the artifact. The onto case uses the prerequisite for `nu = mu`,
and Sections 2 and 4 of the compression artifact for `P = I` and the
homomorphism.

In the strict case a Garden-of-Eden pattern `p` on `Omega` has infinitely many
translates on pairwise disjoint windows, and invariance of `Y` excludes all of
them. Independence gives `mu(Y) <= (1 - |A|^(-|Omega|))^m` for every `m`. The
diagonal projections `e_k` onto the translated patterns commute with each other
and with `P`, with `P e_k = 0`. So `P <= prod(I - e_k)`, and any state extending
`tr` has `omega(P) <= (1 - |A|^(-|Omega|))^m`.

If `tr o Phi` were tracial, conjugation by local permutation unitaries would
make its diagonal restriction `nu` invariant under local permutations, forcing
`nu = mu`. The multiplicative domain of `Phi` is `A_G ∩ {P}'`, which is `A_G` only
when `P = I`, because `A_G` is irreducible.
