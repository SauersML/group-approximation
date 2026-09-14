---
rg: 2
id: hyperbolic-rf-question-reduces-to-one-fixed-host
kind: claim
title: Gromov's question is decided by the hyperbolic quotients of any one fixed non-elementary hyperbolic group
distinct_from:
  hyperbolic-rf-question-equals-non-mf-question: that equates existence of counterexamples with the Kazhdan and non-MF shapes, using some partner; this fixes the host in advance and shows every counterexample shape appears among its own quotients
  olshanskii-g-subgroup-quotient-theorem: that is the imported quotient theorem; this is the reduction built from it together with Kapovich--Wise
---

Let `H` be any non-elementary word-hyperbolic group whose maximal finite normal
subgroup is trivial.  The following are equivalent.

1. Some word-hyperbolic group is not residually finite.
2. For every finite `M subset H` there is a surjection `π : H -> Q`, injective
   on `M`, onto an infinite non-elementary word-hyperbolic group `Q` with no
   nontrivial finite quotient.
3. `H` has an infinite word-hyperbolic quotient with no nontrivial finite
   quotient.

So the search for a counterexample may be confined to the quotients of **one**
group chosen in advance, and a proof for one fixed `H` settles the question.

- **Kazhdan host.**  For `H` a torsion-free cocompact lattice in `Sp(2,1)`
  (`torsion-free-hyperbolic-kazhdan-partner-exists`), every quotient in (2)
  has property (T) and is non-MF.  Every hyperbolic group is residually finite
  iff every infinite hyperbolic quotient of this linear, residually finite
  lattice has a nontrivial finite quotient.
- **Marked limits.**  Taking `M` to be the balls of `H`, a counterexample makes
  `H` a limit, in the space of marked groups, of finite-quotient-free hyperbolic
  quotients of itself.

Proof in `hyperbolic-rf-question-reduces-to-one-fixed-host-proof`.  No novelty
claimed.  Not Lean-verified.
