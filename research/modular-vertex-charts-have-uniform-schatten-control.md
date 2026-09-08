---
rg: 2
id: modular-vertex-charts-have-uniform-schatten-control
kind: claim
title: Exact modular vertex representations admit uniformly controlled Schatten parameterizations
distinct_from:
  word-taylor-remainder-has-a-fourth-moment-bound: that controls ambient generator exponentials, which need not preserve vertex relations; this constructs exact representation-preserving parameterizations and a uniformly bounded lift of every vertex cocycle.
  iwahori-second-order-repair-space-is-empty: that computes the projected Hessian at a compatible pair; this supplies admissible parameterizations at every pair of exact vertex representations, whether or not the two vertices are compatible.
  iwahori-admits-neutral-quadratic-directions: that asks for residual-canceling directions and controlled padding as well as a parameterization; this supplies the parameterization, its derivative estimates, and the lift of supplied flat cocycles.
artifacts:
  - research/artifacts/modular-vertex-admissible-charts-2026-09-08.md
---

Let `rho:SL_2(Z)=C_4 *_(C_2) C_6 -> U(d)` be any representation,
write `S=rho(s)`, `B=rho(b)`, and `Z=S^2=B^3`, so `Z^2=I`.
For anti-Hermitian parameters `H=(H_0,H_4,H_6)` with
`Ad(Z)H_0=-H_0` and `[H_4,Z]=[H_6,Z]=0`, put

```text
Psi_rho(H)(s)=exp(H_0) exp(H_4) S exp(-H_4) exp(-H_0),
Psi_rho(H)(b)=exp(H_0) exp(H_6) B exp(-H_6) exp(-H_0).             (MVC1)
```

This is a globally defined smooth map into exact vertex representations.
There is no bound on the dimension or on the operator norms of the
parameters. For tuples, all Schatten norms below mean the maximum over
the tuple entries, with normalized matrix trace.

Every anti-Hermitian cocycle `c` for `Ad rho` has a real-linear lift
`J_rho(c)=H` whose derivative under `(MVC1)` is `c` and which satisfies

```text
(1/4) max(||c(s)||_p,||c(b)||_p)
   <= ||J_rho(c)||_p <= max(||c(s)||_p,||c(b)||_p)                 (MVC2)
```

for every `1<=p<=infinity`, simultaneously. Consequently a generator
cocycle tuple that is `kappa`-flat in the sense `||c||_6<=kappa||c||_2`
lifts to a parameter tuple that is `4 kappa`-flat. This is a tuple
estimate; it does not assert relative flatness of each parameter entry.

For a word `w` of length `ell>=1`, any parameter base point `H`, and
`j=1,2,3`,

```text
||D^j(w o Psi_rho)(H)[X_1,...,X_j]||_2
    <= (4 ell)^j product_i ||X_i||_(2j).                       (MVC3)
```

More generally the output norm may be any Schatten norm whose reciprocal
is the sum of the reciprocals of the input exponents. In particular
the estimate includes the operator norm version. Movement satisfies

```text
max_{g in {s,b}} ||Psi_rho(H)(g)-rho(g)||_p <= 4 ||H||_p.        (MVC4)
```

Taking the product of the parameterizations for two modular vertices
retains all constants. For their Iwahori mismatch residual `F`, written
as differences of fixed words of lengths at most `L`, `(MVC3)` has
constant `2(4L)^j`. This particular parameterization satisfies the
derivative, movement, and admissibility requirements `(NQ2)` of the
quadratic-direction proposal. This does not prove those properties for
an arbitrary chosen parameterization. The estimates construct no direction
that cancels the projected residual, prove no uniform mismatch right
inverse, and do not control the defect of added blocks. They do not imply
that flat residual-canceling parameters exist universally in this
parameterization. In fact,
`dilution-obstructs-flat-quadratic-iwahori-repair` rules out a universal
sixth-flat square-root parameter step in these coordinates, using a
diluted incompatible character; that input nevertheless has an exact
linear-cost HS repair.

The parameterization has a uniformly bounded right inverse at the
tangent level. A dimension-independent inverse-chart radius in the
normalized HS metric is not asserted, and is not needed for `(NQ2)`.
