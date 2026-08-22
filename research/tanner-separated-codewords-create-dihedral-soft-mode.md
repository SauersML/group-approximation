---
rg: 2
id: tanner-separated-codewords-create-dihedral-soft-mode
kind: claim
title: Tanner-separated codewords create an exact dihedral soft mode
distinct_from:
  sparse-clifford-cycles-refute-average-commutator-rounding: that has sparse strong commutators and no exact parity layer; this has dense but arbitrarily weak commutators while satisfying every parity face exactly
  positive-rate-tanner-tests-have-contextual-models: that uses a finite class-two quotient to stay a fixed distance from commuting tuples; this uses an infinite dihedral quotient to refute a quadratic adjoint gap, while remaining roundable at square-root scale
  repeated-ldpc-adjoint-face-hamiltonian-gap: that asks for a uniform gap for one selected family; this gives a concrete combinatorial condition which every such selection must exclude
---

Let a homogeneous binary Tanner presentation have coordinate reflections
`(x_i)_(i in E)` and bounded parity faces `(T_a)_(a in A)`.  Suppose its
scalar code contains nonzero words `c,d` such that

```text
supp(c) intersect supp(d)=empty,                          (DSM1)
```

and no parity face meets both supports:

```text
T_a intersect supp(c) != empty
  implies T_a intersect supp(d)=empty.                    (DSM2)
```

Equivalently, some nonzero codeword has disconnected support in the Tanner
incidence hypergraph (faces are joined through coordinates in that
codeword's support).  Thus exclusion of this soft mode is the concrete
combinatorial requirement that **every nonzero codeword have connected
Tanner support**.

Then the homogeneous face group surjects onto the infinite dihedral group

```text
D_infinity=<s,t | s^2=t^2=1>.                            (DSM3)
```

Send coordinates in `supp(c)` to `s`, coordinates in `supp(d)` to `t`, and
all other coordinates to `1`.

Consequently the parity-face pinching Hamiltonian has no positive adjoint
gap, even in `M_2`.  For every sufficiently small `theta>0`, put

```text
S = diag(1,-1),
T_theta = R_theta S R_theta^*,                            (DSM4)
```

where `R_theta` is the real planar rotation through `theta`, and compose
`(DSM3)` with `s|->S`, `t|->T_theta`.  Every local face relation is exact,
the common commutant of the coordinate reflections is the scalars, and for
`X=S`

```text
dist_2(X,N')^2=1,
<X,H_theta X>=O(theta^2).                                 (DSM5)
```

Thus no constant `gamma>0` can make `(GFP3)` hold uniformly over exact
local-face representations.  The same model has complete-pair commutator
energy `O(theta^2)`.

This is a soft-mode obstruction to the **spectral-gap proof**, not a
counterexample to same-Hilbert rounding: replacing every `T_theta` by `S`
moves the tuple by `O(theta)` and makes it commute.  Any successful decoder
may therefore have a square-root modulus.  But a route through a uniform
quadratic face-Hamiltonian gap must impose a genuinely operator-visible
indecomposability condition excluding `(DSM1)`--`(DSM2)`; classical distance,
stopping distance, bounded check degree, and LTC soundness alone do not do
so.

The obstruction is compatible with all usual scalar quality parameters.
The direct sum of two copies of any good bounded-check LDPC code has bounded
degree and positive rate, relative distance, stopping distance, and LTC
soundness (with constants reduced by at most the fixed two-block factor),
while the two embedded nonzero codewords satisfy `(DSM1)`--`(DSM2)`.  The
same construction preserves a vanishing-rate hypothesis if the input family
has vanishing rate.
