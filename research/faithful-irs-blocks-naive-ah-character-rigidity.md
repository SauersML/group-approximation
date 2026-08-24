---
rg: 2
id: faithful-irs-blocks-naive-ah-character-rigidity
kind: claim
title: Faithful IRSs give acylindrically hyperbolic groups faithful nonregular characters, but not automatically extremal ones
distinct_from:
  ah-groups-fail-regular-fd-character-rigidity: that produces an extremal nonregular character by pulling back the regular character of a proper ICC quotient, at the cost of a nontrivial kernel; this produces a faithful nonregular fixed-point character without asserting extremality.
  cdi-image-quotient-off-regular-characters-are-ce: that asks for a classification only of faithful extremal characters of the actual CDI image; this explains why the Glasner-Hase theorem obstructs a naive all-character statement but does not itself decide that narrower gate.
artifacts:
  - notes/NONHYPERLINEAR_CHARACTER_REYNOLDS_INTEGRATION_2026-08-24.md
---

Every acylindrically hyperbolic group `G` admits a weakly mixing nontrivial
faithful invariant random subgroup `theta`.  Its fixed-point character is

```text
chi_theta(g)=theta({H<=G:g in H}).                       (FIR1)
```

It is faithful as a character: if `g!=e`, faithfulness of the IRS means that
`g` is not contained almost surely, so `chi_theta(g)<1`.  Hence the GNS
kernel `{g:chi_theta(g)=1}` is trivial.  It is nonregular: because `G` is
countable and `theta` is not concentrated on the trivial subgroup, some
`g!=e` belongs to the random subgroup with positive probability, giving
`chi_theta(g)>0` whereas `delta_e(g)=0`.

Thus no acylindrically hyperbolic source can satisfy the naive assertion
“every faithful character is regular.”  The conclusion must not be silently
strengthened to faithful **extremal** character rigidity.  Although weak
mixing makes the IRS ergodic, an affine image of an extreme IRS need not be
an extreme point of the character simplex without an additional
factoriality theorem.  The surviving CDI image gate is therefore not
refuted by this citation alone.

Primary source: Y. Glasner and A. Hase,
[*Faithful invariant random subgroups in acylindrically hyperbolic groups*](https://doi.org/10.1112/blms.12817),
Theorem 3.4.

