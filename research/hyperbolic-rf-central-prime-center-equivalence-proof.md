---
rg: 2
id: hyperbolic-rf-central-prime-center-equivalence-proof
kind: route
title: Pull back a fixed Deligne central cover along a Belegradek-Osin Rips extension
target: hyperbolic-rf-central-prime-center-equivalence
requires:
  - central-pullback-finite-image-center-criterion
  - hyperbolic-rf-vtf-kazhdan-equivalence
artifacts:
  - research/artifacts/rips-central-pullback-finite-image-centers-2026-09-12.md
---

Fix a prime `p`. The established RF--Kazhdan equivalence turns a
non-residually-finite hyperbolic group into an infinite hyperbolic group
without nontrivial finite quotients. This group satisfies assertion 2 for
every `p`. It is non-elementary because virtually cyclic groups are
residually finite.

Conversely, let `H` satisfy assertion 2. Put `Q=Sp_4(Z)`. Let `E_infty`
be the inverse image of `Q` under the universal covering homomorphism of
`Sp_4(R)`, and write its central kernel as `<t>=Z`. Deligne's theorem
states that every subgroup of finite index in `E_infty` contains `<t^2>`.
Therefore `E_p=E_infty/<t^(2p)>` is a central extension of `Q` by `C_(2p)`
in which the element `z=t^2` has order exactly `p` and belongs to the
finite residual.

Belegradek--Osin's Corollary 1.2, applied to the non-elementary hyperbolic
input `H` and the finitely presented quotient `Q`, gives an exact sequence

```text
1 -> N -> G -> Q -> 1
```

with `G` word-hyperbolic and `N` a quotient of `H`. Thus every finite
image of `N` has center of order prime to `p`. The pullback criterion
applied to `E_p x_Q G` now gives a word-hyperbolic group with a central
order-`p` element in its finite residual. It is not residually finite.

The two literature inputs are used with their exact hypotheses:

- P. Deligne, *Extensions centrales non residuellement finies de groupes
  arithmetiques*, C. R. Acad. Sci. Paris **287** (1978), 203--208, opening
  statement on p. 203, [author PDF](https://publications.ias.edu/sites/default/files/35_ExtensionsCentrales.pdf).
- I. Belegradek and D. Osin, *Rips construction and Kazhdan property (T)*,
  Groups Geom. Dyn. **2** (2008), 1--12, Corollary 1.2,
  [primary preprint](https://arxiv.org/pdf/math/0605553).

The artifact gives the complete pullback calculation and explains the
corresponding transgression condition. Property (T) alone supplies no
vanishing assertion over `F_p` in this argument.
