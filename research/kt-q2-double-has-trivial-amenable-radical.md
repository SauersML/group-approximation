---
rg: 2
id: kt-q2-double-has-trivial-amenable-radical
kind: claim
title: The q=2 Kun--Thom double has trivial amenable radical
distinct_from:
  kt-pair-group-double-is-nonsofic: that imports nonsoficity of Kun--Thom doubles; this is the independent Bass--Serre calculation that removes every amenable normal subgroup in the q=2 instance.
  kt-double-reduced-cstar-is-mf: that is the open norm-microstate problem for the reduced algebra; trivial amenable radical is an established structural input and supplies no matrix approximation.
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
---

For the explicit Kun--Thom pair over `F_2`, with `r,d>=3`, put

```text
Gamma=EL_r(F_2[x_1,...,x_d]),
G=EL_r(F_2[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z),
D=G *_Gamma G.
```

Then the amenable radical of `D` is trivial.

The proof is internal apart from the already-fixed description of the
Kun--Thom pair.  Laurent elementary conjugations show that the normal core of
`Gamma` in `G` consists only of constant scalar matrices; over `F_2` that
core is `{1}`.  Hence the Bass--Serre action of `D` is faithful.  It is also
minimal and non-elementary because both edge embeddings are proper and
`[G:Gamma]=infinity`.  An amenable normal subgroup has an elementary action
on the tree.  If it contains a hyperbolic element, its canonical limit set
has at most two points; normality makes that limit set `D`-invariant, contrary
to non-elementarity.  If all its elements are elliptic but it has no global
fixed vertex, the elliptic-action lemma gives a unique fixed end; normality
makes that end `D`-invariant, with the same contradiction.  It therefore
fixes a nonempty subtree.  Normality makes the subtree `D`-invariant,
minimality makes it the whole tree, and faithfulness makes the subgroup
trivial.
