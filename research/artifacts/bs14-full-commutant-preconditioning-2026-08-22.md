# Finite-period preconditioning of the full BS(1,4) base commutant

The periodic packet normal form has two independent sources of near-unit
adjoint spectrum: long fourth-power orbits and arbitrary scalar return
phases.  Both can be regularized inside the same matrix dimension.

For an exact packet with scalar return phase `v`, choose a nearest `M`th root
of unity `w` and replace only the packet's closing shift edge.  The exact
relation `R S R^{-1}=S^4` survives, while summing over all scalar packets gives

```text
||R-R_M||_2^2 <= pi^2/M^2.
```

After the earlier orbit truncation at length `K`, every orbit block of the
full commutant `{S}'` has basis `E_(j;a,b)`.  The `m`th power of `Ad(R_M)`
multiplies this basis vector by `w_a conjugate(w_b)`, so its order divides
`mM<=KM`.  Therefore

```text
||(1-Ad(R_M))^(-1)||_(fixed-perp)
 <= [2sin(pi/(KM))]^(-1)
 <= KM/4
```

on the whole noncommutative base commutant, including all multiplicity and
monodromy directions.

Combining cycle truncation and phase quantization produces an exact
same-dimensional pair `(R_(K,M),S_K)` with

```text
||S-S_K||_2^2 <= 2pi^2/(9K),
||R-R_(K,M)||_2 <= sqrt(8/K)+pi/M,
```

and the displayed full-commutant inverse.  The executable checker
`experiments/bs14_monodromy_quantization_check.py` verifies exactness,
quantization cost, finite adjoint period, and the spectral-gap bound on random
packet multiplicities.
