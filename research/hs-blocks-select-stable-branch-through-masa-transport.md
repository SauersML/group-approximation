---
rg: 2
id: hs-blocks-select-stable-branch-through-masa-transport
kind: route
title: Transport the scalar-gap block masa by u and kill every model
target: leavitt-steinberg-hs-stable
requires: [hs-expander-block-decomposition, transported-gap-masa-kills-leavitt-hs-models]
---

Along any almost-representation sequence of `G = EL_D(R)` with defects tending
to zero, the corrected `hs-expander-block-decomposition` supplies:

* the fine scalar-gap blocks for `Gamma`, i.e. clauses `(F1)` and `(F2)`; and
* the mass-weighted transport clause `(MW)` for the compressor `u`.

By part (B) of `transported-gap-masa-kills-leavitt-hs-models`, every such
sequence converges to `1` pointwise.  By part (C), `G`, hence
`Q = EL_4(R) ~= G`, is nonhyperlinear, and that is the stable branch.

This route is shorter than `hs-block-decomposition-to-steinberg-stable`.  It
uses neither the coarse ambient blocks, nor the median concentration
`tracial-median-concentration`, nor the majority matching, nor the second
compressor `v`.  The reason is that scalar adjoint gaps make the fine atom
algebra a masa of the Kazhdan relative commutant.  Transport of a masa is
already fatal to every nontrivial model; the permutation proof needs the
median only because expander components are far from maximal abelian.

The converse implication is `hs-block-decomposition-from-stable-branch`; the
two routes form a cycle, recording an equivalence, not a reduction.
