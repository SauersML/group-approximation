---
rg: 2
id: kun-thom-wreath-family-from-tracial-normalization
kind: route
title: "A strict compressor gives a collapsed lamp in every Theorem E binary wreath"
target: kun-thom-wreath-family-is-not-hyperlinear
requires:
  - kazhdan-compression-pairs-normalize-all-tracial-models
  - kun-thom-nonsofic-wreath
artifacts:
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
---

Fix any prime power `q` and any `r,d>=3`, with the rings, actor, subgroup,
and binary wreath in the target. Theorem E, recorded in
`kun-thom-nonsofic-wreath`, says that `Gamma` and `G` are Kazhdan and that
`Gamma` is infranormal but not normal in `G`. In particular they are
finitely generated. The compression semigroup
`P={t in G : t Gamma t^-1<=Gamma}` generates `G` as a group.

Some `t in P` has strict inclusion. Otherwise every element of `P` would
normalize `Gamma`, and the normalizer, being a subgroup containing `P`,
would be all of `G`, contrary to nonnormality. Choose
`gamma in Gamma \ t Gamma t^-1`. A finite generating set of `G` is
expressible by finitely many words in `P` and its inverses. Collecting the
compressors in these words supplies the finite list required by the
normalization prerequisite; one can include the chosen `t` as well.

The two left cosets `gamma t Gamma` and `t Gamma` differ, since equality
would put `gamma` in `t Gamma t^-1`. Their binary lamp product
`b=a_(gamma t Gamma) a_(t Gamma)` is therefore nonidentity. These groups
are countable because the rings are countable and the lamps have finite
support over a countable coset set.

Let `rho:W_(q,r,d)->U(M)` be any homomorphism into any specified tracial
matrix ultraproduct, with no injectivity or trace condition. Set
`D=rho(Gamma)' cap M`. The prerequisite applied to `rho|G` gives
normalization of `D` by `rho(G)`. Since the base lamp is fixed by `Gamma`,
`rho(a_Gamma)` belongs to `D`. Thus `rho(a_(t Gamma))` also belongs to
`D`, and conjugation by `rho(gamma)` fixes it. Lamp covariance and the
order-two lamp relation imply

```text
rho(a_(gamma t Gamma))=rho(a_(t Gamma)),    rho(b)=I.
```

No such `rho` is injective, proving nonhyperlinearity for this parameter
choice. The choice was arbitrary, proving the whole stated family.

## Attribution

This is the Kun-Thom lamp argument applied to the named all-trace
normalization premise. Gabor Kun and Andreas Thom supply the group family
and compression mechanism in [*Nonsofic wreath products of residually finite groups*](https://arxiv.org/abs/2608.06222),
Theorems A and E. Andreas Thom's [conditional construction](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
Theorems 1.2-1.3, supplies the conditional normalization/double mechanism.
The proposed analytic input to that premise is Jihao Liu,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2 / 6.7 and Theorem 1.3 / 7.4. This route extends
the group consequence to all Theorem E parameters; it does not quote
Liu's fixed-parameter Theorem 8.3 as a family-wide result or introduce an
empty-premise import.
