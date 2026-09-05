---
rg: 2
id: unbounded-commutant-coherence-is-the-original-gate
kind: claim
title: Unbounded commutant coherence is exactly the original Jacobson gate
distinct_from:
  bounded-multiplicity-toeplitz-gauges-collapse-head: that proves collapse when every isotypic multiplicity is bounded; this identifies what happens when that hypothesis is removed
  toeplitz-folner-compressions-cannot-retain-jacobson-head: that rules out the literal finite-group carrier; this shows an unbounded commutant can contain an arbitrary microstate independently of that carrier
  scalar-rephased-toeplitz-sections-still-collapse-head: that closes one-dimensional coherence; this proves that unrestricted coherence is not a finite-section subclass at all
---

Use the presentation, head word, Toeplitz section, representation `rho`,
gauges `Z_s in rho(F_N)'`, and tuple

```text
U_s=rho(theta_N(s))Z_s
```

from `bounded-multiplicity-toeplitz-gauges-collapse-head`, but impose no
bound on the isotypic multiplicities.

There are constants `A,B<infinity`, depending only on the fixed
presentation, such that

```text
delta(Z) <= A delta(U),                                 (UCC1)

| ||w(Z)-I||_2-||w(U)-I||_2 | <= B delta(U).            (UCC2)
```

Here `Z=(Z_s)` is viewed as a unitary tuple on the same Hilbert space.
Consequently a head-retaining commutant-gauged Toeplitz sequence exists if
and only if an ordinary head-retaining Jacobson microstate sequence exists.
The implication from left to right is quantitative by `(UCC1)--(UCC2)`;
the reverse implication is exact, using the trivial representation of
`F_N`.

Even requiring `rho` to be faithful does not change the existence
equivalence if its nontrivial carrier is allowed to have vanishing
normalized trace weight. One may add any faithful finite-dimensional
representation of `F_N` and then overwhelm it by arbitrarily many copies
of the trivial isotype carrying the original microstate.

Thus unbounded commutant coherence supplies neither a construction nor an
extra rigidity theorem: it is a repackaging of the unsolved global
dimension-free head modulus. The genuinely different surviving ansatz is
a perturbation outside `rho(F_N)'`, where generators can mix inequivalent
finite-group isotypes and carrier/gauge word separation fails.

DERIVATION
commutant-gauge-equivalence-and-faithful-padding-proof
