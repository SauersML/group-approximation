---
rg: 2
id: commuting-nonscalar-readouts-force-coset-four-cycles
kind: claim
title: Commuting nonscalar readouts through two subgroups meeting in the central phase force a four-cycle in their coset graph, and functionally dependent readouts force a larger intersection
distinct_from:
  finite-readout-bcs-decoders-are-phase-surviving-local-colimits: that characterizes finite-readout decoders as phase-surviving colimits; this constrains the subgroup geometry inside one context group that any commuting pair of readouts imposes.
  group-corner-decoders-split-into-coset-and-matrix-readouts: that splits decoders by abelian versus matrix readouts; this shows that even nonabelian readouts of commuting variables cannot sit in subgroups whose coset graph has no four-cycle.
  slofstra-zhang-high-girth-phase-survival: that protects the phase by high incidence girth for abelian solution groups; this is a local constraint on context groups that limits how much curvature the context groups themselves can supply.
---

**ESTABLISHED** by `commuting-nonscalar-readouts-coset-four-cycles-proof`.
Not independently reviewed; elementary, no novelty claimed.

## Setting

`A` is a finite group, `J <= Z(A)` a central cyclic subgroup of order `n`,
`omega` a faithful character of `J`, and

```text
p_omega = (1/n) sum_(k=0)^(n-1) conj(omega(J^k)) J^k   in C[A].
```

For subgroups `H, K <= A` containing `J`, the **coset multigraph**
`Gamma(A; H, K)` has vertex set `A/H` disjoint union `A/K` and one edge for
each coset `gJ in A/J`, joining `gH` to `gK`. It is bipartite. Its girth is
`2m(H,K)` with `m(H,K) in {1, 2, 3, ...} or +infinity`; `m = 1` exactly when
`Gamma` has parallel edges, i.e. when `H cap K` is strictly larger than `J`.

## Statement

**(CN1) Commuting nonscalar readouts.** Suppose `H cap K = J`, and
`x in C[H] p_omega`, `y in C[K] p_omega` satisfy `xy = yx`, with neither `x`
nor `y` in `C p_omega`. Then

```text
HK cap KH  is strictly larger than  H union K,
```

and `Gamma(A; H, K)` contains a four-cycle, so `m(H, K) = 2`.

**(CN2) Functionally dependent readouts.** If `x in C[H] p_omega` also lies in
`C[K] p_omega`, then `x in C[H cap K] p_omega`. In particular a nonscalar
readout that lies in both algebras forces `H cap K` strictly larger than `J`,
so `m(H, K) = 1`. This applies whenever a context forces `y_(v')` to be a
function of `y_v` (equality, negation, any `y_(v') in C*(1, y_v)`), with
`H = H_v`, `K = H_(v')`.

## Consequence for local data

In finite local data `D` for a Boolean constraint system, as in
`finite-readout-bcs-decoders-are-phase-surviving-local-colimits`, the readouts
`y_v, y_w` of two variables sharing a context commute. So for every context
`c` and every pair `v != w` in `V_c` with nonscalar readouts,

```text
m(H_v, H_w) <= 2   inside A_c.                                   (CN3)
```

Context constraints therefore cap the Gersten--Stallings-type angle a context
group can supply at a pair of nonscalar variables at the right-angle value.
Coset geometries of larger girth, such as generalized polygons inside groups
of Lie type, cannot host commuting nonscalar readouts of two variables whose
subgroups meet only in the phase.
