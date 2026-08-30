---
rg: 2
id: stw72-purely-infinite-radical-reduction
kind: claim
title: Every weakly purely infinite counterexample has a canonical hereditarily bad quotient
distinct_from:
  stw72-chain-ideal-cover-wpi-is-purely-infinite: that is a positive local-to-global theorem when good ideals cover the algebra; this theorem works for every algebra and removes the closed sum of all purely infinite ideals to isolate the exact residual obstruction.
  stw72-scattered-primitive-spectrum-wpi-is-purely-infinite: that eliminates a topological positive class; this theorem says that every possible counterexample has a quotient with no nonempty open positive-class patch at all.
artifacts:
  - research/artifacts/stw72-purely-infinite-radical-audit-2026-08-30.md
---

For a C-star algebra `A`, define

```text
P_pi(A)=closure(sum{I : I is a purely infinite closed ideal of A}).
```

Then `P_pi(A)` is itself purely infinite and is the unique largest purely
infinite ideal of `A`.

If `A` is weakly purely infinite and

```text
B=A/P_pi(A),
```

then `B` is weakly purely infinite and has no nonzero purely infinite ideal.
For weakly purely infinite `A`, `P_pi(A)` is also the unique largest ideal
having the Global Glimm Property.  Accordingly, every nonzero ideal of `B`
fails the Global Glimm Property; in Cuntz-semigroup terms, its Cuntz
semigroup must fail ideal-filteredness or property (V).
Consequently:

* `A` is purely infinite exactly when `B=0`;
* if `A` is a counterexample to the weak-to-plain implication, then `B` is
  a nonzero counterexample and every nonzero closed ideal of `B` is again a
  weakly-but-not-plain purely infinite algebra;
* the general implication in Problem LXXII is equivalent to its restriction
  to weakly purely infinite algebras having no nonzero purely infinite ideal.

The reduction preserves nuclearity, separability, and exactness whenever
they are present.  Thus it applies without changing the category asked for
in Problem LXXII.
