---
rg: 2
id: kt-normalizing-witnesses-centralize-compressors
kind: claim
title: A witness that normalizes the Kun--Thom group and centralizes its polynomial subgroup centralizes the whole group
distinct_from:
  relative-wall-commutant-growth: that is the exact equivalence between a relative wall and properness of a commutant inclusion in any target group; this excludes one explicit class of witnesses, those normalizing the ambient group, by a three-line centralizer computation.
  ce-stabilizer-criterion-needs-no-trace: that turns relative embeddability into the search for a commutation stabilizer in some Connes-embeddable target; this rules out every normalizing element as the witness in that search for the Kun--Thom pair.
---

**ESTABLISHED.** Let `Gamma <= G` with `C_G(Gamma) = 1` and `Gamma`
infranormal in `G`. Let `U` be a group, `sigma : G -> U` an injective
homomorphism, and `h in U` with

```text
h sigma(G) h^(-1) = sigma(G),        [h, sigma(Gamma)] = 1.
```

Then `h` commutes with `sigma(G)`. So its commutation stabilizer in `G` is all
of `G`, never `Gamma` when `Gamma != G`.

This holds for the binary Kun--Thom Theorem E pair
`Gamma = EL_r(F_2[x_1,...,x_d]) <= G = EL_r(F_2[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z)`,
`r,d >= 3`, because there `C_G(Gamma) = 1` (proved in the derivation).

**What it rules out as a witness of `kt-subgroup-is-a-ce-commutation-stabilizer`:**

- an element of an amenable extension `G rtimes K`, whose centralizer in `G` is
  the fixed subgroup of the corresponding automorphism;
- a direct factor, or any overgroup element normalizing `G`;
- a unitary `x in U(M)` implementing an automorphism of an injective image
  `sigma(G)`.

These are exactly the overgroups on which hyperlinearity permanence is
available for free: amenable extensions, direct products, and automorphic
twists. A stabilizer witness must move `sigma(G)` off itself, as the stable
letter of the centralizer HNN group does.

DERIVATION
kt-normalizing-witnesses-proof
