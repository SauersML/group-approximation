---
rg: 2
id: boundary-char-two-simple-kazhdan-is-not-hyperlinear
kind: claim
title: Boundary simple Kazhdan groups over finite fields of characteristic two are not hyperlinear
distinct_from:
  boundary-action-simple-kazhdan-group-is-hyperlinear: That asks for hyperlinearity over a general finite field; this is a negative assertion restricted to characteristic two, for every boundary rank d at least two.
  boundary-simple-kazhdan-hyperlinear-iff-binary-leavitt-el: That is a characteristic-by-characteristic equivalence which decides neither side; this is the negative characteristic-two conclusion.
  binary-leavitt-unit-group-is-not-hyperlinear: That concerns the Leavitt unit group; this concerns the boundary elementary groups modulo their centers, into which a Leavitt subgroup embeds.
artifacts:
  - research/artifacts/liu-leavitt-consequences-audit-2026-09-20.md
---

For every finite field k of characteristic 2, every d>=2 and N>=3, the
group

```
S_boundary(d,k,N) = EL_N(LC(boundary F_d,k) crossed F_d) / Z(EL_N)
```

is not hyperlinear. Here LC denotes locally constant functions and the
crossed product is the algebraic crossed product for the boundary action.
No assertion about odd characteristic or characteristic zero is included.
No finite-presentation conclusion is asserted here.

## Attempts

2026-09-20: `boundary-char-two-nonhyperlinear-from-leavitt` transfers the
negative Leavitt branch using the existing same-characteristic equivalence.
Only its explicit subgroup direction is needed. Since the Leavitt negative
branch still depends on open Kazhdan internality, this conclusion is also
conditional in the graph. It should not be used as a blanket refuter of
every finite-field instance of the broader boundary hyperlinearity claim.

**Attribution.** The proposed analytic input is Jihao Liu,
[*Nonhyperlinear groups exist* (2026-09-20)](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
Theorems 1.2/6.7; Proposition 3.1 provides the related expectation-lift
criterion. This boundary conclusion passes through Cairn's conditional
Leavitt application of Liu's theorem and the existing boundary equivalence.
Neither this boundary theorem nor that Leavitt deduction is claimed in Liu's
paper. The earlier September 8 Cairn two-use argument and September 13
boundary reduction retain their separate credit and proof dependencies.
