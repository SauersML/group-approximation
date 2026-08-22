---
rg: 2
id: central-hecke-controlled-multipaths-remain-sectorwise
kind: claim
title: Central Hecke-controlled multipaths remain sectorwise and cannot fold the arithmetic double
distinct_from:
  spherical-quadrature-tensors-through-clifford-folner-windows: That treats separated spherical and Clifford test families; this permits additive mixed operators controlled by spherical atoms on the same matrix carrier.
  finite-projective-sector-groupoids-have-conjugate-absorbers: That cancels projective arrow cocycles; this proves the additional central-control decomposition after the arrows are absorbed.
  rank-one-additive-swap-cycles-only-read-isotropy-holonomy: That analyzes one noncentral two-path corner swap; this treats arbitrary finite central-controlled sums and identifies why they have no path interference.
---

# Central Hecke-controlled multipaths remain sectorwise

Let `D` be a finite-dimensional commutative algebra with atomic projections
`p_1,...,p_m`, and let `B` be any unital tracial algebra commuting with `D`.
For unitaries `V_(a,j) in B`, put

```text
W_j=sum_(a=1)^m p_a V_(a,j).                              (CHM1)
```

These are genuine additive multipath operators on one carrier, but their
paths never interfere.  Each `W_j` is unitary, and every noncommutative word
`q` in the `W_j` and elements of `D` has the unique sector decomposition

```text
q=sum_a p_a q_a,                                          (CHM2)
```

where `q_a` is obtained by evaluating every control coefficient at the
character `a` and retaining only the corresponding `V_(a,j)`.  Consequently

with `t_a=tau(p_a)` and `tau_a(x)=tau(p_a x)/t_a`,

```text
||q||_2^2=sum_a t_a||q_a||_(2,tau_a)^2,
tau(q)=sum_a t_a tau_a(q_a).                              (CHM3)
```

In particular no Hilbert--Schmidt relation assembled from finitely many such
centrally controlled multipaths can charge an operator incompatibility
between different `a`-branches.  A trace-square test sees only the modulus
square of the scalar convex combination in `(CHM3)`; it contains no
off-diagonal block term.  Any finite list of those scalar moments can be
included in the atomic quadrature data.

## Arithmetic application

Take `D` to be an atomic quadrature algebra for a finite list of spherical
Hecke moments of

```text
SL_3(Z) < SL_3(Z[1/2]).
```

Take the `V_(a,j)` to be bounded-depth Clifford/type transports induced by
the elementary root words and the six Weyl-conjugate denominator moves.  On
a coweight Folner box, complete these transports at the boundary and cancel
their finite projective cocycles by conjugate doubling.  Formula `(CHM3)`
then shows that every fixed family of relations among operators `(CHM1)` has
vanishing normalized Hilbert--Schmidt defect whenever it is valid in each
native sector.  The spherical moments still converge to their regular
values, including the nonfolded lazy Hecke value `43/168`.

This strictly extends the commuting tensor escape: the elementary/Hecke
paths may now be selected by different spherical atoms inside one additive
operator.  Centrality nevertheless turns the sum into an orthogonal direct
sum.

Thus the smallest surviving arithmetic incidence cannot be a controlled sum

```text
sum_a p_a V_a.
```

It must make at least one control projection noncentral relative to another
authenticated chart, or compress two distinct elementary-matrix paths into
the same matrix block so that cross terms survive.  Equivalently, a useful
mixed trace-square coefficient must contain an overlap `p_a V p_b` which
cannot be diagonalized in one common spherical atomic algebra.  This is the
precise first place where the tensor/Folner model no longer applies.

That first place is necessary but not sufficient.  The explicit rotated-flip
model in `two-sl3-shell-charts-have-a-rotated-flip-escape` has two genuinely
noncommuting shell charts and an exact full matched transporter, yet retains
the positive mismatch `(41/42)cos(t)^2`.  Two-chart data have only principal
angles and transporter gauge.  The next candidate must close a three-chart
loop and compare at least two returns on one corner.
