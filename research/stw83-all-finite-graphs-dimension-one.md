---
rg: 2
id: stw83-all-finite-graphs-dimension-one
kind: claim
title: Every finite graph C-star algebra has nuclear dimension at most one
distinct_from:
  stw83-problem-lxxxiii-graph-nuclear-dimension: that includes arbitrary graphs; this is the exact finite core to which the general problem reduces.
  stw83-finite-graphs-are-complete-test: that established reduction proves this finite statement is sufficient for the root but does not prove it.
---

**OPEN.**  For every finite directed graph `F`,

```text
dim_nuc(C*(F))<=1.
```

By [[stw83-finite-graphs-are-complete-test]], this finite statement is
equivalent to the full all-graphs assertion in STW Problem LXXXIII.

## Attempts

The finite case is not covered by a generic ideal-extension estimate: splitting
a finite graph algebra into its AF and purely infinite pieces gives an upper
bound of two unless one can reuse a colour across the extension.  One sharp unresolved test after the existing full-corner reductions is the
canonical circle-to-circle Toeplitz family
`C*(S^N tensor 1, K tensor C(T))`.  Its known construction uses three
colours; the missing step is a finite-set-adaptive two-colour approximation
that carries genuinely circle-varying information on the plateau diagonal.
Solving this family would settle the circle-ideal/circle-quotient direction,
but not by itself the finite-graph claim or STW Problem LXXXIII: the independent
circle-ideal/Kirchberg-quotient direction remains open as recorded in
[[stw83-two-non-k-extension-directions-remain-open]].

The firewall [[stw83-commuting-cone-two-colour-firewall]] now rules out
two broad implementations.  A uniformly local commuting functional calculus
in the coefficient phase and the Toeplitz cutoff would two-colour
`Cone(T)=D^2`, contradicting its dimension two.  A whole-corner scheme
whose second colour is block diagonal across a constant plateau would make a
complementary matrix circle zero-dimensional.  The still-open escape is
strictly noncommutative and finite-set adaptive: extinguish coefficient
variation before the scalar transition, then transport the two colours
through a long buffer with stage-dependent matrix supports.  No such
relative Brake--Winter recolouring is currently proved.
