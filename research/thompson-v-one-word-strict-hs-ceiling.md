---
rg: 2
id: thompson-v-one-word-strict-hs-ceiling
kind: claim
title: Bound one nontrivial Thompson-V word strictly below regular Hilbert--Schmidt energy
artifacts:
  - research/artifacts/thompson-v-one-word-ce-frontier-2026-08-21.md
distinct_from:
  cyclic-carrier-energy-stability: that seeks equality with an exact finite-dimensional energy ceiling for a general cyclic carrier; the Thompson-V character simplex means any strict bound below the regular value automatically collapses to that equality.
  thompson-v-not-lef: that rules out finite local embeddings and operator-norm-separated exact models; this is a normalized-HS statement about approximate unitary representations.
  thompson-pauli-prefix-rounding-has-polynomial-cost: that rounds addressed Pauli data carried by V prefix words; this target concerns the bare group V and one ordinary group word.
---

Fix a finite presentation `V=<X|R>` and one word `w!=1`. Prove that there are
`epsilon>0` and `delta>0` such that every finite-dimensional unitary tuple
`U=(U_x)_(x in X)` satisfying

```text
max_(r in R)||r(U)-I||_2<delta
```

also satisfies

```text
||w(U)-I||_2^2<=2-epsilon.                              (TV2)
```

Equivalently,

```text
lim_(delta->0) sup_(def_R(U)<=delta)||w(U)-I||_2^2<2.
```

By `thompson-v-ce-one-word-trace-face-is-binary`, `(TV2)` is equivalent to
nonhyperlinearity of `V`: it is a concentrated one-word reformulation of the
root problem, not an established gap.

## Attempts

- Fournier-Facio--Rangarajan prove uniform Ulam stability of `V` with a
  linear estimate for unitary targets equipped with submultiplicative norms
  (operator norm and unnormalized Frobenius/Schatten norms). Normalized HS is
  not submultiplicative with dimension-free constants, and their paper
  explicitly leaves Hilbert--Schmidt approximability of Thompson groups open.
  Their fragmentation and bounded-generation mechanism is motivation, not a
  theorem implying `(TV2)`.
- The Dudko--Medynets character theorem removes every intermediate limiting
  trace once a strict ceiling is proved, but it supplies no quantitative
  control on approximate representations by itself.
- Infinite-dimensional Cuntz/permutative representations do not furnish
  finite matrix microstates and therefore neither prove nor refute `(TV2)`.
- Full normalized-HS stability would prove `(TV2)` but is unnecessary. A
  successful argument may control only the one scalar moment
  `Re tr(w(U))`.
- No dimension-free group-algebra positivity or sum-of-squares identity valid
  in all tracial representations can prove `(TV2)`, because the exact regular
  representation has energy `2`. The missing estimate must be genuinely
  finite-matrix/Connes-embeddability sensitive.
