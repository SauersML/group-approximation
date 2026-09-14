---
rg: 2
id: thompson-f-dyadic-action-is-extensively-amenable
kind: claim
title: The action of Thompson's group F on the dyadic rationals is extensively amenable
distinct_from:
  thompson-f-is-amenable: that is amenability of F, which implies this claim (every action of an amenable group is extensively amenable); the converse is not known.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that is amenability of certain Schreier graphs; extensive amenability of an action is strictly stronger than amenability of its Schreier graph in general.
artifacts:
  - research/artifacts/ideas-wildcards-2026-09-14.md
---

**OPEN.** The action of `F` on the dyadic rationals `D ⊂ (0,1)` is extensively amenable. That is, some
`F`-invariant mean on the finite subsets of `D` gives full weight to the subsets containing any given
finite set.

## Consequences

- **Co-amenability of Jones' subgroup.** Through `jones-subgroup-coamenable-if-dyadic-action-extensively-amenable`
  it gives `jones-subgroup-is-co-amenable-in-thompson-f`, answering the question in Aiello–Brothier–Conti
  Remark 4.7 positively.
- **A refutation proves F nonamenable**, by Lemma 2.1 of Juschenko–Matte Bon–Monod–de la Salle
  (`affine-lamplighter-amenable-iff-extensively-amenable`).

## Known obstacles

- **The base graph is transient.** Mishchenko (arXiv:1512.03083) shows the simple random walk on the dyadic
  Schreier graph has nontrivial Poisson boundary. So the recurrence criterion of Juschenko–Nekrashevych–de la
  Salle does not apply.
- **The action is primitive.** Point stabilizers in `(0,1)` are maximal subgroups (Aiello–Nagnibeda,
  arXiv:2103.07885, abstract). So there is no nontrivial `F`-quotient of `D` along which to apply the extension
  principle.
