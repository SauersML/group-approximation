---
rg: 2
id: weak-soficity-survives-every-corpus-obstruction-proof
kind: route
title: Collect the four mechanisms carried by the sofic group E and the two carried by Glebsky permanence
target: weak-soficity-survives-every-corpus-obstruction
requires: [literal-group-sofic, finitely-presented-sofic-non-mf, weakly-sofic-not-sofic, kun-thom-clifford-cover-weakly-sofic]
artifacts:
  - research/artifacts/non-weakly-sofic-audit-2026-08-17.md
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

**The bridge used four times.**  A sofic group is weakly sofic: a symmetric
group with normalized Hamming metric is a finite group with a bi-invariant
metric, so a `(Φ,ε,1-ε)`-permutation model is a `(Φ,ε,α)`-model in the sense
of Glebsky--Rivera Definition 4.1, with `α` any constant below the separation
that `isSofic_iff_weak` pins.  `literal-group-sofic` therefore makes `E`
weakly sofic outright, and every property of `E` becomes a property
compatible with weak soficity:

- **non-MF.**  `finitely-presented-sofic-non-mf` is the conjunction itself:
  `E` is finitely presented, sofic and not MF.
- **not residually finite.**  `E`'s central mark is nontrivial and killed by
  every homomorphism to a finite group, so `E` is not residually finite; it
  is still sofic.
- **an element killed by every finite quotient.**  Same word, taken as its
  own mechanism because it is the one that most resembles the certificate of
  `non-weakly-sofic-word-certificate`.  See
  `literal-mark-conjugacy-width-unbounded` for the exact reason the
  resemblance fails.
- **violating a finite quasi-identity valid in all finite groups.**  The
  manuscript's Horn sentence `⋀_(r∈R) r(x_1,...,x_8)=1 ⟹ w(x_1,...,x_8)=1`
  holds in every MF group, hence in every finite group, and fails on the
  canonical tuple of `E`.  `E` is nevertheless weakly sofic; the structural
  reason is that a weakly sofic group is a subgroup of a *quotient* of a
  direct product of finite groups, and quasi-identities do not survive
  quotients.

**The permanence bridge used twice.**  Glebsky's 2023 theorem — weakly sofic
normal subgroup with residually finite quotient gives a weakly sofic
extension — supplies the other two rows, and both are already established
nodes: `weakly-sofic-not-sofic` for the Kun--Thom wreath `W` (nonsofic,
weakly sofic) and `kun-thom-clifford-cover-weakly-sofic` for the Clifford
cover `E_S`, whose Corollary 10 in
`notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md` realizes the marked
anticommuting wall inside a metric ultraproduct of finite groups with
bi-invariant metrics, radical word surviving.

**The conclusion is a non-implication in each row**, so no further argument is
needed: a mechanism that holds in a weakly sofic group cannot imply failure
of weak soficity.
