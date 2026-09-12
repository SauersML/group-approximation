---
rg: 2
id: opnorm-coordinatewise-capacity-diagonal
kind: claim
title: Uniform addressed capacity challenges let the proof choose depth after seeing matrix dimension
distinct_from:
  same-model-supercritical-clifford-trigger: that asks the group computation itself to read the candidate dimension and activate a larger challenge; this theorem shows no internal dimension sensor is needed if one fixed presentation already exposes every finite challenge rank with uniform operator-norm soundness.
  halt-now-certificate-area-still-needs-a-crossing-envelope: that treats a moving word window whose defect control deteriorates with the candidate; here the entire challenge tower is controlled by one fixed defect modulus independent of challenge depth, so the diagonal crossing obstruction disappears.
  fixed-mark-forbids-uniform-clifford-table-area: that rules out one particular way of obtaining the uniform tower, namely bounded-area full Clifford tables for a fixed finite mark; this is an abstract capacity implication and permits other challenge geometries.
---

Let `Gamma=<S|R>` be finitely presented and let `w` be a word. Suppose there
are constants

```text
beta>0, epsilon_0>0, C<infinity,                              (OCD1)
```

a function `F:N->N` with `F(N)->infinity`, and for every `N>=1` a finite
challenge packet `Q_N` of free words, such that:

1. **uniform address control:** every unitary tuple `U` satisfies

```text
max_(q in Q_N) ||q(U)-I||_op <= C Def_R(U)                    (OCD2)
```

with the same `C` for every `N`;

2. **finite-capacity soundness:** if `U` is `d`-dimensional,

```text
||w(U)-I||_op >= beta,
max_(q in Q_N)||q(U)-I||_op < epsilon_0,                      (OCD3)
```

then

```text
d >= F(N).                                                    (OCD4)
```

Then there is no finite-dimensional tuple `U` satisfying

```text
Def_R(U) < epsilon_0/C,
||w(U)-I||_op >= beta.                                       (OCD5)
```

Indeed, after `U` and its dimension `d` are fixed, the **proof** chooses
`N` with `F(N)>d`; the fixed tuple already satisfies the depth-`N` challenge
by `(OCD2)`, contradicting `(OCD4)`.

Consequently, if `w!=1` in `Gamma` and MF separation for `w` can be normalized
to the fixed threshold `beta` (for example by the standard bounded tensor/
power normalization), then `Gamma` is not MF.

This is an MF-specific diagonal principle. The group never receives `d` as
input. The candidate dimension is used only metamathematically to select which
already-present challenge packet defeats that candidate.
