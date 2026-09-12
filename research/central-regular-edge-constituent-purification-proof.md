---
rg: 2
id: central-regular-edge-constituent-purification-proof
kind: route
title: Concentrate dimension-weighted constituent measures at an extreme trace
target: central-regular-edge-constituents-are-fell-pure
requires: []
---

For a countable group `H`, the trace space `Tr(H)` is a compact metrizable
convex subset of the product disk `D^H`.  If `mu` is a probability measure
on `Tr(H)`, its coordinatewise barycenter

```text
b(mu)(h)=integral_(Tr(H)) phi(h) dmu(phi)               (CRF1)
```

again belongs to `Tr(H)`.  The barycenter map is continuous for weak
convergence because every coordinate evaluation is continuous.

We first prove that an extreme trace `tau` has only the trivial representing
measure.  Suppose `b(mu)=tau`.  For any Borel set `A` with
`0<mu(A)<1`, let `tau_A,tau_(A^c)` be the barycenters of the two normalized
restrictions.  Then

```text
tau=mu(A) tau_A+(1-mu(A)) tau_(A^c).                    (CRF2)
```

Extremality gives `tau_A=tau_(A^c)=tau`.  If `mu` were not `delta_tau`, some
real or imaginary coordinate evaluation on `Tr(H)` would be nonconstant on
a set of positive `mu`-measure.  Cutting that bounded real random variable
at a level strictly between two points of its essential range gives a set
`A` for which its two conditional means differ.  This contradicts
`tau_A=tau_(A^c)`.  Since the countable coordinate evaluations separate
traces, one obtains

```text
b(mu)=tau and tau extreme  implies  mu=delta_tau.       (CRF3)
```

For `(CRP1)`, complete reducibility gives

```text
b(mu_n)=tr(rho_n(.))/d_n ->tau.                         (CRF4)
```

If `(CRP2)` failed, some open neighborhood `U` of `tau` and a subsequence
would satisfy `mu_n(U^c)>=epsilon>0`.  Compactness of the probability-measure
space gives a further weak limit `mu`.  Equations `(CRF1)` and `(CRF4)` give
`b(mu)=tau`, while the Portmanteau inequality for the closed set `U^c` gives
`mu(U^c)>=epsilon`.  This contradicts `(CRF3)` and proves `(CRP2)`.

For fixed `D`, normalized characters of all representations of dimensions
at most `D` form a compact subset `K_D` of `Tr(H)`: each
`Hom(H,U(k))` is compact in the product topology and normalized trace is
continuous.  If the GNS representation of `tau` is infinite-dimensional,
then `tau notin K_D`.  Choose a neighborhood of `tau` disjoint from `K_D`
and apply `(CRP2)`.  This proves the bounded-dimension assertion.

In the central-regular Iwahori sector, `(ICO6)` of the cited outlier artifact
gives pointwise central-regular character convergence separately for the two
exact edge restrictions.  To remove the central sign explicitly, use
`SL_2(Z)^ab ~= C_12`: the central involution maps to the unique element of
order two, so a one-dimensional modular character `kappa` satisfies
`kappa(z)=-1`.  Its restriction to `B` twists the negative sector to one on
which `z` acts trivially; use the trivial twist in the positive sector.
The representations then descend to `B/<z>`.  This quotient is `Z*C_2`,
which is ICC, so its group von Neumann algebra is a factor and its regular
trace is extreme.  The preceding theorem applies separately to the two
exact edge restrictions.  A diagonal choice over an exhausting sequence of
finite word sets, shrinking character tolerances, and increasing dimension
bounds produces `W_n,D_n` in `(CRP4)`.

Finally, orthogonality and unitarity give the exact marginal identities

```text
sum_j ||P_(n,i) V_n Q_(n,j)||_2^2=tr(P_(n,i)),
sum_i ||P_(n,i) V_n Q_(n,j)||_2^2=tr(Q_(n,j)).          (CRF5)
```

Thus the overlap mass meeting a bad row or column is at most the sum of the
two bad marginals, hence is `o(1)`.  The mixed-energy threshold theorem also
loses only `o(1)` mass.  Their intersection has mass `1-o(1)`, and every
type appearing there obeys the dimension and character conditions in
`(CRP6)`.  This proves the Iwahori purification statement without asserting
an integral block matching or a mixed spectral gap.
