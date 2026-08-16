---
rg: 2
id: stage-one-radical-from-involutive-endpoint
kind: route
title: Read the collapse commutator as a lamp difference and transport it
target: stage-one-lamp-difference-radical
requires: [hnn-one-site-lamp-is-a-torsion-compression-witness, compression-torsion-collapse]
artifacts:
  - GroupApproximation/Sofic/AscendingHNNTelescopeRadical.lean
---

## Why sufficient

**The identity.**  `[a, b] = (a b a^-1) b^-1`, and conjugating the one-site
lamp at the witness site by a base element moves the site and keeps the value.
So the commutator is `inl(single (gamma . tGamma) k) * inl(single tGamma k)^-1`,
which is the lamp difference of the two sites.  Nothing analytic enters.

**Transport.**  Conjugation by `inr g` acts on the lamp base through
`lampAut g`, which is a homomorphism sending `single x k` to `single (g . x) k`.
Applied to a difference it translates both sites at once.  The collapse defect
is a normal subgroup, so every translate of a base-move difference is again in
it -- and the coset action is transitive, so "every translate" means every
site.

**Radical membership.**  The witness lamp is an involutive compression witness
whenever the lamp value is an involution, the base copy inside the wreath
product inherits property (T) from the base, and the stable letter compresses
it by the HNN relation.  Those are the three hypotheses of the involutive
endpoint, whose conclusion is unconditional radical membership.

**Nontriviality.**  Properness gives an element outside the image of the
self-embedding whose base move genuinely separates two sites, and one-site
lamps at distinct sites with a nontrivial value differ.

**Equality.**  The reduction theorem turns "invisible subgroup with MF
quotient" into "the MF radical is exactly that subgroup".

## What this route does not do

It stops at one stage: the site pairs it reaches are exactly those differing by
the level `-1` copy of the base.  The remaining levels are **not** obtained by
iterating it -- they are obtained by running the same criterion on the
level-`n` Kazhdan copy with compressor `t^n`, which is
[[level-copies-are-kazhdan-and-compressed]].
