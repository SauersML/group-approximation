---
rg: 2
id: leavitt-24k-models-avoid-blockwise-error-basis-normalizers
kind: claim
title: Approximate 24k models stay a fixed normalized-HS distance from every blockwise error-basis-normalizing tuple
distinct_from:
  leavitt-24k-feasibility-has-a-uniform-gap: that asks for a gap against ALL unitary tuples, which would prove nonhyperlinearity; this proves a gap only against the blockwise error-basis-normalizing class and its normalized-HS neighbourhood, and settles nothing about tuples outside it.
  clifford-direct-sum-dilution-forces-an-exact-good-block: that is the exact block-selection statement for Pauli-valued curvatures, with no perturbation and no group input; this is uniform in block count and dimension, survives a normalized-HS perturbation of the whole tuple because its comparison class is entered by an infimum, and uses the MF obstruction to make the 3-cycle scalar on the surviving block.
  leavitt-24k-first-relation-has-exact-finite-model: that evaluates the first relation and shows it alone admits an exact GL_3(F_8) solution; this consumes the necessary-bound half of that claim and adds the exclusion of a whole model class.
  error-basis-normalizer-has-a-sharp-trace-gap: that is the one-matrix linear-algebra input; this is the group-level consequence for approximate models of the binary Leavitt unit group.
artifacts:
  - research/artifacts/leavitt-error-basis-normalizer-obstruction-2026-09-08.md
---

**ESTABLISHED.** Let `C_D` be the class of four-tuples in `U(D)`
preserving one orthogonal decomposition and normalizing, on each block,
one group-labelled unitary error basis; block count and dimensions are
unrestricted and per-block scalar phases are free. The class contains all
finite Pauli/Clifford normalizers, their direct sums, and identity tensor
padding. Put

```text
delta(X) = inf_(Y in C_D) max_g ||X_g - Y_g||_(2,D).
```

Let `T` be the finite kernel set of
`mf-obstruction-gives-a-finite-c-killing-relation-set`, enlarged by the
word `r_*`, and let `R_P` be the seven internal relators of
`P = C_3 * C_2^3`. With `S = T union R_P`, `M = |S|`,
`L = max(8, max_(r in S)|r|)`, `gamma = sqrt(2 - sqrt 2)`,

```text
A_0 = 1/2 + 2 sqrt M / gamma,      B_0 = 12 + 2 L sqrt M / gamma,
```

every exact `P`-tuple `X` with `tr_D(C^2) = 0` -- in particular every
regular-factor `24k` tuple -- satisfies

```text
A_0 max_(r in T) ||r(X) - I||_(2,D) + B_0 delta(X) >= 1/sqrt 2.
```

So any sequence of regular-factor models whose `T`-defects tend to zero
keeps `liminf delta >= 1/(sqrt 2 B_0) > 0`. Hyperlinear models of the
binary Leavitt unit group, if they exist, cannot be built from
increasingly large finite Pauli/Clifford blocks, nor from anything within
a fixed normalized-HS distance of that architecture.

**This does not decide hyperlinearity.** It is an exclusion of a model
class, not a gap against arbitrary unitary tuples; the missing step is
recorded as
`hyperlinear-leavitt-models-reduce-to-error-basis-normalizers`.
The constants are explicit only once a `T` is exhibited, since the
prerequisite proves existence without a witness.

DERIVATION
leavitt-24k-blockwise-normalizer-exclusion-proof
