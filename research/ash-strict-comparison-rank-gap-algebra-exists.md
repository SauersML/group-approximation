---
rg: 2
id: ash-strict-comparison-rank-gap-algebra-exists
kind: claim
title: A simple unital ASH algebra with strict comparison whose rank functions are not dense exists
distinct_from:
  stw27-strict-comparison-non-pure-algebra-exists: that asks for any nuclear strict-comparison algebra that is not pure; this asks for an approximately subhomogeneous one with an explicit failure of rank density, which implies failure of purity.
  stw23-rank-problem-counterexample-exists: that asks for one unrealized rank with no comparison hypothesis and no class restriction; this demands strict comparison, ASH building blocks, and failure of even approximate realization.
  simple-unital-ash-algebras-realize-ranks-approximately: that is the positive assertion that rank functions are dense on every simple unital ASH algebra; this is a candidate for its failure, strengthened by strict comparison.
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

**OPEN.** There is a unital simple separable infinite-dimensional ASH
algebra `A` with strict comparison of positive elements, a continuous strictly
positive affine function `f` on `T(A)`, and `eta > 0`, such that every
`y in M_infty(A)_+` has `|d_tau(y) - f(tau)| >= eta` at some trace `tau`.

Such an `A` is not pure: pure algebras have stable rank one, and stable rank
one realizes all ranks.  So `A` refutes part (1) of STW XXVII and, since `A`
is nuclear, Toms--Winter (`stw27-counterexample-via-ash-gluing-rank-gap`).

## Attempts

- **Gluing obstruction as the mechanism.**  In a recursive subhomogeneous
  block the attaching map forces the boundary values of every positive element.
  Suppose the forced support is a nontrivial subbundle over `X_k^(0)` and the
  admissible rank drop `delta n_k` is below about half of `dim X_k`.  Then no
  extension over `X_k` matches a prescribed rank profile.  Sustaining this
  through a simple limit requires twisted attaching maps with no slow
  dimension growth, and tracial weight on the drop loci that no admissible
  choice avoids.
- **Why it is hard.**  The same characteristic classes that obstruct extension
  normally break comparison, as in Villadsen's examples, where small twisted
  supports are not subequivalent to larger trivial ones.  A witness has to
  obstruct extension of rank profiles without producing a pair `a, b` with
  `d(a) < d(b)` and `a` not below `b`.  No construction is known.  The
  untwisted diagonal case cannot give a witness if the staggering argument
  recorded on `simple-unital-ash-algebras-realize-ranks-approximately` closes.
