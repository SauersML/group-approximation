---
rg: 2
id: stw22-dim1-factor-bundles-have-uniform-traces
kind: claim
title: Countably generated factorial bundles over one-dimensional bases have only uniform traces
distinct_from:
  stw22-one-dimensional-trivial-field-trace-continuity: that theorem puts every fibre in one fixed factor; the present theorem allows arbitrary nontrivial bundles and varying finite-factor fibres, using stabilization of the intrinsic L2 module as the common selection space.
  stw22-zero-dimensional-factor-bundles-have-uniform-traces: that theorem needs no countable-generation hypothesis but uses disjoint clopen patching; the present theorem crosses connected one-dimensional bases by Hilbert-module stabilization and nonconvex selection.
  stw22-intrinsic-local-replication-colouring-reduction: that is conditional on exact local replication; the present theorem proves global replication in dimension at most one for every countably generated factorial bundle.
artifacts:
  - research/artifacts/stw22-stabilized-l2-selection-audit-2026-08-30.md
---

Let `K` be a compact Hausdorff space with covering dimension at most one,
and let `(M,E)` be a factorial tracially complete C-star algebra over `K`.
Thus `C(K)` is contained centrally in `M`,

```text
E:M -> C(K)
```

is the tracial expectation, and the `2`-norm fibre `M_x` is a finite factor
with trace `tau_x=ev_x o E`.  Suppose that the Hilbert `C(K)`-module

```text
H=completion of M for ||a||_(2,u)=||E(a*a)||^(1/2)
```

is countably generated.  Then every norm/`2`-norm fibre gap `K_x/J_x` has
no nonzero bounded positive trace.  Consequently every tracial state on
`M` is uniquely of the form

```text
a |-> integral_K E(a)(x) dmu(x)
```

for a probability measure `mu` on `K`, and is continuous for the uniform
`2`-norm.

The countable-generation hypothesis is automatic when the operator-norm
unit ball of a C-star subalgebra is uniform-`2`-norm dense in `M_1` and that
subalgebra is separable.  In particular, the theorem applies to the
factorial Bauer W-star bundles arising as uniform tracial completions of
separable C-star algebras whenever their compact extreme boundary has
covering dimension at most one.

The new point is that no common ambient factor, local trivialization, or
continuous field of support projections is assumed.  Stabilization embeds
the intrinsic `L^2` field as a complemented subfield of the trivial Hilbert
bundle `K times ell^2`.  The exact weighted-copy sets in the varying factor
fibres then form a lower-semicontinuous, uniformly locally path-connected
family of closed subsets of the one complete metric space `ell^2`.  A
one-dimensional selection produces the copies needed to annihilate every
gap trace.
