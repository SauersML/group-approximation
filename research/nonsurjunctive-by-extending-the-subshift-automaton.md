---
rg: 2
id: nonsurjunctive-by-extending-the-subshift-automaton
kind: route
title: Read the proper-subshift self-embedding as a full-shift counterexample
target: leavitt-unit-group-nonsurjunctive
requires: [leavitt-kernel-annihilator-strict-self-embedding]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

**INVALID.**  Recorded so that the most tempting reading of the repository's
Leavitt code has an address, and a kill.

## The proposed step

`X = ker(pi)^perp` is a closed shift-invariant subset of `F_2^G`, and the
four-site rule `T_a` restricts on it to an injective non-surjective
continuous equivariant map.  One reads that as an injective non-surjective
cellular automaton over `G` and concludes that `G` is not surjunctive.

## Why it fails

Surjunctivity is a statement about the **whole** full shift `A^G`.  Extending
a map from an invariant subshift to the ambient shift need not preserve
injectivity, and here the natural extension provably does not: `a` has four
terms, so `eps(a) = 0`, so right multiplication by `a` misses `1` and its
dual `T_a` is non-injective on `F_2^G`.

That kills the obvious extension.  What kills the route is
`subshift-self-embedding-carries-no-surjunctivity-content`: the same
construction runs verbatim over a finitely generated free group, which is
surjunctive.  The premise is therefore compatible with the negation of the
conclusion, and no repair of the lift can help.

The same shortcut at ring level is refused by
`direct-finiteness-not-inherited-by-quotients`, which is the reason the
Kaplansky lane is posed as a lifting problem rather than read off the
surjection.  Both refusals have the same shape.

The algebra behind the failure is exact.  Injectivity of `T_a` restricted to
`X` is surjectivity of right multiplication by `a` **modulo** `ker(pi)`;
injectivity of `T_a` on the full shift is surjectivity of right
multiplication by `a` on **all** of `S`.  Surjectivity after quotienting does
not imply surjectivity before it, and the difference is precisely the open
claim `left-invertible-lift-of-s0-in-leavitt-group-algebra`.
