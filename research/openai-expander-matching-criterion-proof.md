---
rg: 2
id: openai-expander-matching-criterion-proof
kind: route
title: Decompose twice, match by bounded medians, select one component, complete and repair
target: openai-expander-matching-criterion
requires: [kun-expander-decomposition-formalized, kun-thom-expander-centralizer-formalized, openai-bounded-median-component-matching]
artifacts:
  - official/counterexample.tex
---

## Why sufficient

Assume `G` sofic, with one approximation `p_n : G -> Sym(Y_n)`, amplified so
that `N = |Y_n| -> oo`.  Fix a finite symmetric `S_Gamma` containing `1` and
adjoin the `t_i^(±1)` to get `S_G`; normalize inverse labels to inverse
permutations, which costs `o(N)` vertices.

**The two decompositions** come from the first prerequisite, applied to the
restricted approximation of `Gamma` and to the approximation of `G`.  They are
two generally different partitions of the same vertex set, with unlabelled
reference graphs -- no compatibility between them may be assumed, and the
number of components in either may grow without bound.

**The matching** is the third prerequisite: transported components
`p_i(C)` land almost inside single `Gamma`-components, of almost the same
size, and distinct transported components take distinct targets.

**From the matching to `J`.** Take `i = 1`.  Injectivity makes every fixed
`Gamma`-word preserve each `p_1(C)` at almost every vertex.  Since
`t_1 J t_1^(-1) <= Gamma`, each `J`-generator is `t_1^(-1) (an element of
Gamma) t_1`; conjugating the preservation statement by `p_1^(-1)` therefore
shows that the `J`-generators preserve the **original** `Gamma`-components at
almost every vertex.  The `Gamma`-generators preserve them already.  So both
factors of `Gamma x J` act, off a negligible set, inside single
`Gamma`-components.

**Selection and repair.** Only finitely many multiplication, commutation and
distinctness tests are in play for a given finite window, each failing on a
negligible fraction; so one `Gamma`-component may be chosen on which all of
them hold outside a negligible subset.  Restrict both generator actions to it,
complete the partial permutations arbitrarily, discard a negligible set to
restore uniform expansion, and complete once more.  `Gamma cap J = {1}` and
`[Gamma, J] = 1` make the result a sofic approximation of `Gamma x J`, and by
construction its `Gamma`-generator graph is a **single** expander on the whole
of the new vertex set.

**The obstruction.** That is exactly the hypothesis of the second
prerequisite, which concludes that `J` is LEF.

## Where the hypotheses are consumed

Property (T) of `Gamma` twice: once for its own decomposition, once for the
Kazhdan pair the second prerequisite needs.  Property (T) of `G` only to
decompose the ambient generators -- which is why the chapter's current version
can drop it in favour of assuming the expanding approximation directly.
`G = <Gamma, t_1, ..., t_m>` is what makes the ambient decomposition see every
generator.  `Gamma` infinite keeps the components from being uniformly
bounded.  The distinguished compressor `t_1` is the only one whose matching is
used; the others are needed only so that the ambient graph is a graph for all
of `G`.
