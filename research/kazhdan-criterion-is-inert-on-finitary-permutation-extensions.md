---
rg: 2
id: kazhdan-criterion-is-inert-on-finitary-permutation-extensions
kind: claim
title: The normal-Kazhdan criterion can never fire inside a finitary permutation extension of an MF group
distinct_from:
  normal-kazhdan-defect-non-mf: that is the criterion itself, a sufficient condition for a corona homomorphism to kill a normal Kazhdan subgroup of the compression defect; this proves the condition is unsatisfiable in one structural family, so the criterion is not merely unproved there but inert.
  locally-finite-centralizer-derived-subgroup-is-mf-invisible: that is the criterion which does fire on that family, needing a locally finite centralizer and commuting compressed conjugates instead of a normal Kazhdan subgroup; this explains why that substitution was forced rather than convenient.
  wreath-candidate-embeds-in-finitary-permutation-extension: that embeds the wreath candidate in a finitary permutation extension to gain a hyperfinite base algebra, a von Neumann-algebraic move; this is a group-theoretic no-go about which killing criterion can apply to such an extension, and involves no factor.
artifacts:
  - research/artifacts/finitary-linear-vs-permutation-kazhdan-criterion-2026-09-08.md
---

**ESTABLISHED.**  Let `V` be a countable MF group acting on a countable set
`X`, and put

```text
P = Sym_fin(X) x| V.                                                  (KI1)
```

Let `H <= P` be **any** subgroup, `L <= H` with property (T), and `A` a normal
subgroup of `H` with property (T) satisfying `A <= D_H(L)`.  Then

```text
A = 1.                                                                (KI2)
```

So `normal-kazhdan-defect-non-mf` has no nontrivial instance anywhere inside
`P`: not for `H = P`, and not after passing to a subgroup in the hope of
finding a normal Kazhdan subgroup there.  The criterion is **inert** on this
family, rather than merely unproved.

**What this explains.**  The dyadic finite-perturbation group
`dyadic-perturbation-group-is-sofic` is exactly of the form `(KI1)`, and its
radical is computed in `dyadic-perturbation-group-mf-radical-is-finitary-alternating`
by `locally-finite-centralizer-derived-subgroup-is-mf-invisible` -- the
criterion that needs a locally finite centralizer and commuting compressed
conjugates, and no normal Kazhdan subgroup at all.  `(KI2)` says that
substitution was forced.  Any future finitary permutation example must use
that criterion or a new one; reaching for the Kazhdan criterion there cannot
work, whatever the action.

**Scope.**  `V` is assumed MF, which is what makes the projection `P -> V`
useless to the criterion; nothing is claimed when `V` is not MF.  The
statement is about which criterion can apply, not about whether `P` is MF --
`P` is frequently not, and `dyadic-perturbation-group-mf-radical-is-finitary-alternating`
is the case in point.

The companion positive statement, that replacing `Sym_fin` by `GL_fin` over
`F_2` makes the same criterion fire, is
`finitary-linear-extension-kazhdan-defect-kills-kernel`.
