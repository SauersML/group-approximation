---
rg: 2
id: selector-correlated-direct-power-router-proof
kind: route
title: Pair each selector character with one packet coordinate and apply Schur's lemma
target: selector-correlated-direct-power-router
requires:
  - full-conjugation-table-cancels-router-multiplicity
---

Each `sigma_a` is irreducible because it is the external tensor product of
one irreducible representation of a direct factor with trivial
representations of the other factors and one character of `A`.  Distinct
`a` give distinct restrictions to `A`, so the corresponding primitive
central projections are orthogonal.

On the `a`-coordinate, precomposition by `theta` changes `rho` to

```text
k |->rho(r_a k r_a^(-1)).
```

This is unitarily equivalent to `rho`, with intertwiner `rho(r_a)`, and
`theta` fixes the `A`-character.  Hence `theta` fixes the isomorphism class
of `sigma_a`, and therefore fixes `q_a` in `C[L]`.

Let `pi` be any representation of `(SDR3)`.  On the `q_a`-isotypic carrier,
write the restriction of `pi|L` as `sigma_a tensor I`.  The covariance
relations say that

```text
(rho(r_a)^* tensor I) pi(t)
```

commutes with `sigma_a(L) tensor I`.  Schur's lemma therefore makes it
`I tensor V_a`, proving `(SDR4)`.  Every diagonal constant `Delta(k)` acts
as `rho(k) tensor I` on this carrier.  Substitute `(SDR4)` into `W`.  Moving
the copies of `V_a` through the packet constants costs nothing, and the zero
exponent sum cancels all of them.  What remains is exactly `(SDR5)`.

For robustness, evaluate the character formula for `q_a` on the approximate
finite table of `L`.  Finite Fourier orthogonality makes these operators an
`O(eta)` orthogonal central PVM.  Average the covariance defect over `L` on
the `q_a` block.  The trace-preserving finite conditional expectation onto
the commutant shows that

```text
(rho(r_a)^* tensor I) pi(t)
```

is `O(eta)` from that commutant.  Telescope the fixed balanced word, exactly
as in `full-conjugation-table-cancels-router-multiplicity`.  Every averaging
set and every word is fixed and finite, so the total constant is computable
and independent of the ambient dimension.

In the hyperoctahedral specialization, the balanced truth word gives `z` on
the forbidden coordinates and `1` on the allowed coordinates.  Equation
`(SDR5)` therefore gives the claimed predicate readout.  Integer-valued
signed-permutation characters make the standard primitive-idempotent formula
rational.
