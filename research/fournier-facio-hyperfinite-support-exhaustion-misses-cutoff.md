---
rg: 2
id: fournier-facio-hyperfinite-support-exhaustion-misses-cutoff
kind: claim
title: Hyperfinite exhaustion of an infinite support component does not trigger the Fournier--Facio cutoff fence
invalidates:
  - fournier-facio-amenable-hyperfinite-exhaustion-closes-overlap
distinct_from:
  fournier-facio-generator-support-components-escape-cutoffs: That rules out positive charge on actual support components of uniformly bounded size; this proves that finite subrelations exhausting one infinite support component do not produce such a component.
  fournier-facio-block-dimension-escapes-every-charge-cutoff: That starts with an exact common finite-block system modulo the charged null ideal; this separates that exact datum from finite-block approximants whose positive boundary charge merely tends to zero.
  near-representation-amenability-dichotomy: That asks whether a Kazhdan near representation has positive-charge rigid structure; this shows only that an abstract hyperfinite exhaustion of its support relation would not supply the bounded charged structure needed here.
---

**ESTABLISHED EXHAUSTION FIREWALL.**  Even the following strongest naive
conclusion from amenability would not contradict
`fournier-facio-generator-support-components-escape-cutoffs`:

```text
the support relation is an increasing union of finite equivalence relations.
                                                               (HFSC1)
```

There is an exact amenable representation with regular character and a
purely singular invariant diagonal state whose generator support graph has
one infinite component, while `(HFSC1)` holds with uniformly finite classes
at every stage.

Take the bilateral shift `T` on `ell^2(Z)` and a translation-invariant free
probability charge `mu` on `Z`.  A coherent nonintegral `2`-adic sequence of
cuts gives nested interval relations `R_n`, every class of `R_n` having size
`2^n`, and

```text
union_n R_n = Z x Z.                                  (HFSC2)
```

The cyclic block shift `T_n` on the `R_n`-classes differs from `T` only at
one residue class modulo `2^n`.  Consequently

```text
phi_mu((T-T_n)^*(T-T_n)) = 2^(1-n) > 0,               (HFSC3)
```

although the left side tends to zero.  Thus every finite exhaustion stage
has positive charged boundary.  No `T_n` is equal to `T` modulo the charged
null ideal, so its finite classes are not the actual support components to
which the cutoff theorem applies.

This pinpoints the missing uniformity.  Hyperfinite exhaustion gives
arbitrarily small charged boundaries; the established cutoff fence needs one
fixed comparison family with **zero** charged boundary.  Amenability or
hyperfiniteness alone does not promote the former to the latter.  The
remaining Fournier--Facio positive face must therefore be attacked by a
uniform null-boundary theorem, a Cartan/monomialization theorem, or a direct
obstruction on the genuinely infinite support component—not by bare
hyperfinite exhaustion.

There are exactly two tempting but invalid quantifier exchanges here.
First, `inf_n mu(boundary R_n)=0` does not produce an `n` with null boundary;
`(HFSC3)` realizes this failure.  Second, even if a limiting decomposition
has finite classes, finite additivity does not turn

```text
X=union_m {x: class_size(x)<=m}
```

into positive charge for one bounded-size stratum.  The latter is precisely
the dimension-at-infinity alternative already isolated by
`fournier-facio-block-dimension-escapes-every-charge-cutoff`.  Thus neither
passing to a finite exhaustion stage nor passing to its countable union
reaches the hypothesis of the cutoff theorem.

Proof: `fournier-facio-hyperfinite-exhaustion-calibration-proof`.
