---
rg: 2
id: stw22-rank-one-scattered-fibre-gaps-are-tracefree
kind: claim
title: Rank-one scattered Bauer fibres have cofinite-corona, bounded-trace-free gaps
distinct_from:
  stw22-nuclear-convergent-sequence-has-nonzero-tracefree-gap: that theorem computes one convergent-sequence endpoint; the present theorem identifies the same corona at every locally rank-one point and treats all compact scattered bases of Cantor--Bendixson height at most two.
  stw22-norm-fibre-gap-is-the-trace-obstruction: that abstract theorem identifies the obstruction for a central bundle; the present theorem eliminates it for a concrete nuclear class by an explicit local calculation.
artifacts:
  - research/artifacts/stw22-rank-one-scattered-gap-audit-2026-08-30.md
---

Let `U` be an infinite-dimensional UHF algebra with unique trace, let
`R=pi_tau(U)''`, let `X` be compact Hausdorff, and let `M` be the uniform
tracial completion of

```text
A=C(X) tensor U.
```

Suppose that `x in X` has a clopen neighbourhood `V` such that
`D=V\{x}` is discrete.  Equivalently, `V` is the one-point
compactification of `D`.  If `D` is infinite, then the norm/`2`-norm fibre
gap at `x` is canonically

```text
K_x/J_x ~= I_D
 := { (a_d) in product_(d in D) R:
          ||a_d||_2 -> 0 along the cofinite filter }
       / direct-sum_D^c0 R.                              (RSG)
```

The algebra `I_D` has no nonzero bounded positive trace.  When `D` is
countably infinite, it is nonzero.  Thus every gap at a point of
Cantor--Bendixson rank one is bounded-trace-free, even inside a compact
space of larger scattered rank.

Consequently, if `X` is compact scattered and `X^(2)` is empty, then every
tracial state on `M` is uniquely

```text
a |-> integral_X tau(a(t)) dmu(t)
```

for a probability measure `mu` on `X`; in particular it is continuous for
the uniform `2`-norm.  This proves the Problem XXII conclusion for the
uniform completion of `C(X) tensor U` over every compact scattered base of
Cantor--Bendixson height at most two.  More generally, for any scattered
`X`, a failure in this trivial-field model can only be supported at
`X^(2)`.
