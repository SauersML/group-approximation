# STW LXXXVII: diagonal-bimodular localization no-go audit (2026-08-30)

## Result

Let `D=ell^infinity(X) subset C*_u(X)=A`.  The canonical diagonal
expectation is the unique bounded `D`-bimodule retraction `A->D`.  More
strongly, every bounded `D`-bimodule map `S:A->A` fixing `D` satisfies

```text
E_X S=E_X.
```

Normalized property-A Schur multipliers are c.p.c., `D`-bimodular, and fix
the diagonal.  They can replace operators by controlled-propagation
operators, but applying the diagonal expectation afterwards returns exactly
the same diagonal as before localization.  Thus they preserve, rather than
repair, the previously established exact order-zero gaps: `1/2` for the
commutative two-point packet and `1` for noncommutative matrix packets.

## Proof check

For each singleton diagonal projection `p_x` and each `a in A`, a
`D`-bimodule retraction `R:A->D` must satisfy

```text
p_x R(a) p_x=R(p_x a p_x)=a_(xx)p_x.
```

These singleton coordinates determine an element of `D`, proving `R=E_X`.
No density argument, positivity assumption, or approximation is involved.
The composite `E_X S` is again a `D`-bimodule retraction, which proves the
factorization identity.  Substitution into the two exact gap computations
gives the quantitative conclusions verbatim.

There is also a stable form.  For a c.p.c. map `R:A->D`, let
`delta_D` measure its norm defect from the identity on `D`, and let `delta_c`
measure its bimodule defect at all singleton corners.  Reading the `x`-th
coordinate through `p_x a p_x=a_(xx)p_x` gives

```text
norm(R-E_X)<=delta_D+delta_c.
```

The exact packet gaps then show that `R` cannot retain the Hadamard
commutative packet as order zero unless `delta_D+delta_c>=1/2`, and cannot
retain any canonical `M_n` packet unless `delta_D+delta_c>=1`.  Thus even an
approximate-bimodule replacement must incur a fixed, scale-independent
defect before it can preserve the relevant colours.

Literal sparsification cutdowns occupy the opposite endpoint.  For a proper
subset projection `p=chi_Omega`, the map `a->E_X(pap)` is still exactly
diagonal-bimodular, but its restriction to `D` has norm defect one from the
identity (test a diagonal projection supported in `X minus Omega`).  Thus a
single sparse corner cannot be a perturbative global diagonal recovery.
Families of sparse corners could still be recombined before averaging; the
present theorem does not rule out that genuinely multi-corner construction.

## Boundary

This theorem blocks the most direct attempt to combine property-A metric
localization with diagonal averaging.  It does not show that every possible
localization is diagonal-bimodular, and it does not rule out extracting a
coarse cover directly from the non-diagonal supports of order-zero maps.
Accordingly it is a route obstruction, not a proof of either remaining
lower-bound seam in Problem LXXXVII.
