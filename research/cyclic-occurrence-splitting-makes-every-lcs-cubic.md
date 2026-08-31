---
rg: 2
id: cyclic-occurrence-splitting-makes-every-lcs-cubic
kind: claim
title: Cyclic equality splitting makes every binary LCS occurrence-three without changing its solution group
artifacts:
  - research/cubic-occurrence-splitting-tietze-proof.md
distinct_from:
  degree-two-operator-ports-are-boundary-edges: that proves occurrence at most two is graph incidence and has no perfect model gap; this shows the jump to occurrence three recovers all exact LCS solution groups.
  one-triple-variable-lcs-has-no-perfect-model-gap: that proves one triple-used variable is still tame; this construction may use one triple variable for every high-degree source variable.
  slofstra-solution-group-embedding-preserves-marked-involutions: that embeds a finitely presented group into an LCS solution group; this is a postprocessing of any LCS which preserves its entire marked solution group.
---

Every finite binary LCS `L` has an effectively constructible binary LCS
`L^(3)` in which every variable occurs in at most three equations and

```text
Gamma_(L^(3)) isomorphic to Gamma_L
```

by an isomorphism fixing the central involution `J`.

If a variable `x` occurs `d>=3` times, replace its occurrences by
`x_1,...,x_d` and add the even equality cycle

```text
x_1 x_2 = 1,
x_2 x_3 = 1,
...
x_d x_1 = 1.
```

Each copy occurs once in an old equation and twice in equality equations,
so its occurrence is three.  Each equality relator between involutions
implies `x_i=x_(i+1)`; the added commutation is then redundant.  Eliminating
`x_2,...,x_d` by Tietze moves recovers the original presentation exactly.
Variables of occurrence one or two can be left unchanged.

Hence the exact expressiveness boundary is sharp:

```text
maximum occurrence 2  -> graph incidence; perfect qc iff perfect finite q,
maximum occurrence 3  -> every finite LCS solution group.
```

In particular, Slofstra's solution-group embeddings and perfect
commuting-versus-finite separations can be transferred verbatim to
occurrence-three LCS presentations.  The resource is not one isolated
triple variable—ruled out separately—but a network of diagonal equality
cycles.

This is an exact presentation theorem only.  Approximate equality errors
can accumulate around a cycle of length `d`, so the construction does not
claim a degree-independent Hilbert--Schmidt soundness constant.

`expander-equality-splitting-is-a-robust-occurrence-four-compiler` repairs
this quantitative loss by spending one more occurrence per copy.  Its
rotating-Pauli example also proves that the degree-two equality cycle here
has an unavoidable quadratic Poincare degeneration.
