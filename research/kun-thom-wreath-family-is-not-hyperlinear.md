---
rg: 2
id: kun-thom-wreath-family-is-not-hyperlinear
kind: claim
title: "Every binary coset wreath over the Kun-Thom Theorem E family is nonhyperlinear"
distinct_from:
  kun-thom-lamp-wreath-is-not-hyperlinear: "That fixes q=2 and r=d=3 and records Liu's explicit marked element and finite approximation obstruction; this quantifies over every prime power q and every r,d>=3 and is a downstream corollary of universal normalization."
  kun-thom-nonsofic-wreath: "That establishes nonsoficity for infranormal Kazhdan pairs; this excludes normalized Hilbert-Schmidt approximation for the entire explicit Theorem E family."
  kazhdan-compression-pairs-normalize-all-tracial-models: "That is universal relative-commutant normalization for all rigid pairs and all homomorphisms; this is its concrete group consequence for binary coset wreaths over the polynomial/Laurent family."
artifacts:
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
---

For every prime power `q` and integers `r,d>=3`, set

```text
R_+=F_q[x_1,...,x_d],     R=F_q[x_1^(+-1),...,x_d^(+-1)],
Gamma=EL_r(R_+),          G=EL_r(R) rtimes SL_d(Z),
W_(q,r,d)=(direct_sum_(G/Gamma) C_2) rtimes G.
```

The integer matrix group acts by monomial substitutions; `Gamma` is the
polynomial subgroup in the first factor, and `G` acts on the binary lamps
by left translation of left cosets. The claim is that every displayed
countable group `W_(q,r,d)` is not hyperlinear.

More precisely, for each of these pairs there exist a strict compressor
`t` and `gamma in Gamma \ t Gamma t^-1` such that the nonidentity element
`b=a_(gamma t Gamma) a_(t Gamma)` is killed by every homomorphism from
`W_(q,r,d)` to the unitary group of every tracial matrix ultraproduct.

## Attribution

The analytic input is Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Theorem 1.2 / 6.7, followed by his conditional normalization
Theorem 1.3 / 7.4. The conditional normalization and double construction
are credited to Andreas Thom, [*A conditional construction of a nonhyperlinear group and the centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
Theorems 1.2-1.3. The family of pairs and the lamp argument are due to
Gabor Kun and Andreas Thom, [*Nonsofic wreath products of residually finite groups*](https://arxiv.org/abs/2608.06222),
Theorems A and E. This family-wide conclusion is a downstream corollary
of the named normalization premise, not the verbatim statement of Liu's
Theorem 8.3, which fixes `q=2,r=d=3`.

## Attempts

2026-09-20: use Theorem E to obtain an infranormal, nonnormal Kazhdan pair
for each parameter choice. Universal normalization then collapses a
strict-compressor lamp product. The route records these prerequisites and
does not independently import the claimed analytic theorem.
