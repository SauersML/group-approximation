---
rg: 2
id: andre-guirardel-sharp-t-actor-audit
kind: claim
title: Andre-Guirardel supply the sharp property-T actor but not the finite-presentation interface
distinct_from:
  sharp-two-t-actor-gives-fp-host: that is the conditional exact compiler under finite presentation and a finitely generated point stabilizer; this audits the closest published actor against those hypotheses.
artifacts:
  - research/artifacts/andre-guirardel-sharp-t-actor-2026-08-21.md
---

André and Guirardel, *Finitely generated simple sharply 2-transitive
groups*, Compositio Mathematica 160 (2024), Theorems 1.1 and 1.4, construct
an infinite group `A` which is:

```text
two-generated, simple, property (T), and sharply 2-transitive.           (AGA1)
```

Thus their actor has exactly the algebraic and spectral properties needed
in `sharp-two-t-actor-gives-fp-host`: no proper finite-index subgroup,
perfectness, a uniform Kazhdan gap, and exactly two diagonal orbits on the
countable action set.

The published theorem says **finitely generated**, not finitely presented.
Its construction uses iterative small-cancellation quotients to obtain the
final two-generated group.  The paper also does not provide the additional
finite generation of a point stabilizer required by the standard
permutational-wreath finite-presentation criterion.  Therefore `(AGA1)`
cannot presently be substituted into the conditional compiler.

This is an unusually close host candidate: the remaining algebraic search
is not for an expander action, simplicity, or two-transitivity.  It is for
either

```text
(a) a finitely presented version of the Andre-Guirardel actor with a
    finitely generated point stabilizer, or
(b) a different finite presentation of its augmentation-lamp extension
    that does not require those two properties.                           (AGA2)
```

Even after `(AGA2)`, normalized-HS same-basis rounding remains necessary.
