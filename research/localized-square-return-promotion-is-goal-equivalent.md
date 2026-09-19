---
rg: 2
id: localized-square-return-promotion-is-goal-equivalent
kind: claim
title: Bare localized square-return promotion is exactly finitely presented nonhyperlinearity
distinct_from:
  localized-square-return-wandering-promotion: that asks for one concrete marked promotion; this audits its unrestricted existential content and shows that, without a nonvacuity condition on the finite models, it is exactly the root goal.
  canonical-reverse-kleene-compiler-is-goal-equivalent: that treats a uniform recursive family indexed by machines; this is the one-group localized square-return analogue.
---

**ESTABLISHED.**  The following existence statements are equivalent.

1. There is a nonhyperlinear group.
2. There are a finitely presented group `Gamma`, a nonzero finite-support
   projection `q in C[Gamma]`, and an infinite-order word `w in Gamma` such
   that every full canonical-trace matrix microstate sequence satisfies

   ```text
   ||(w(U)^2-1)q(U)||_2 -> 0.                         (LGE1)
   ```

The implication `2 => 1` is
`compressed-finite-order-wandering-is-terminal`: the finite support of `q`
and the infinite order of `w` make `(w^2-1)q` nonzero in the regular group
algebra, whereas `(LGE1)` kills its canonical microstate norm.

For `1 => 2`, use
`nonhyperlinearity-has-a-finite-presentation-witness` to choose a finitely
presented nonhyperlinear group `K`, and put

```text
Gamma=K times Z,              q=1,              w=z,
```

where `z` generates the `Z` factor.  Hyperlinearity passes to subgroups, so
`Gamma` is nonhyperlinear.  Equivalently, by
`nonhyperlinear-group-has-finite-canonical-microstate-witness`, one fixed
finite canonical window of `Gamma` has a positive all-dimensions defect.
There is therefore no full canonical-trace matrix microstate sequence for
`Gamma`, and the universal assertion `(LGE1)` holds over the empty collection
of such sequences.  The unit is a nonzero finite-support projection and `z`
has infinite order.

The reverse implication is deliberately vacuous.  It supplies no
finite-coordinate decoder or matrix-only return law.  Consequently the bare
existential reading of `localized-square-return-wandering-promotion` does not
lower the root problem.  A useful version must construct its presentation
independently of a nonhyperlinear seed or require a nonvacuous family of
finite models on which the localized return is actually proved.
