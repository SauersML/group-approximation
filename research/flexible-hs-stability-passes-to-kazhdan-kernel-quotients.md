---
rg: 2
id: flexible-hs-stability-passes-to-kazhdan-kernel-quotients
kind: claim
title: Flexible HS stability passes to quotients by Kazhdan normal subgroups
distinct_from:
  flexible-p-stability-passes-to-fg-normal-quotients: that is Alekseev--Thom's permutation statement, where finite generation of the kernel suffices; this is the unitary normalized-HS statement, where the kernel needs property (T) so that averaged almost invariance becomes near invariance.
  alekseev-thom-stability-finite-actions-boundary: that records Alekseev--Thom Theorem A(ii), where a Kazhdan normal kernel passes stability in finite actions; this is the Hilbert--Schmidt analogue for flexible stability, with a direct proof.
  hyperlinear-flexibly-hs-stable-group-is-residually-finite: that derives residual finiteness from flexible HS stability of a hyperlinear group; this transports flexible HS stability itself from a group to a quotient.
artifacts:
  - research/artifacts/kazhdan-hyperbolic-hs-candidates-2026-09-12.md
---

**ESTABLISHED.** Let `Γ` be finitely generated and let

```text
1 -> N -> Γ -> Q -> 1
```

be exact with `N` having property (T). If `Γ` is flexibly Hilbert--Schmidt
stable, then so is `Q`.

Flexible HS stability is the Dogon--Vigdorovich notion (their Definition 1.2):
every asymptotic representation `σ_n: Q -> U(d_n)` in normalized
Hilbert--Schmidt norm admits genuine representations `λ_n: Q -> U(D_n)`,
`D_n >= d_n`, with `||σ_n(x) - P_n λ_n(x) P_n||_(2,d_n) -> 0` for every `x`.

The proof has four steps:
1. compose `σ_n` with the quotient map and apply stability of `Γ`;
2. use a Kazhdan pair of `N` to push the stable corner into the `N`-fixed
   subspace;
3. note that the genuine representation factors through `Q` on that subspace;
4. absorb the `o(d_n)`-dimensional defect in a trivial summand.

The Hamming analogue with a Kazhdan kernel is Alekseev--Thom, arXiv:2512.15494,
Theorem A(ii). A bounded search on 2026-09-12 found no printed unitary version:
the Cairn graph, arXiv:2512.09180, and the Becker--Lubotzky and Dogon--Vigdorovich
abstracts.

## Consequences

- `flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear`: every
  quotient of a flexibly HS-stable group by a Kazhdan normal subgroup is
  residually finite or non-hyperlinear.
- Proving a hyperbolic Kazhdan group that maps onto `Q` with a Kazhdan kernel
  (a Belegradek--Osin cover) flexibly stable is never easier than proving `Q`
  stable.

DERIVATION
flexible-hs-kazhdan-kernel-quotient-proof
