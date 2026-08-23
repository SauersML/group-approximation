---
rg: 2
id: bs14-bounded-moments-cannot-extract-congruence-level
kind: claim
title: No fixed finite family of BS14 word or Hecke moments extracts the moving congruence level
distinct_from:
  bs14-global-atoms-are-moving-congruence-restrictions: that identifies exact atoms as moving congruence restrictions; this proves a fixed normalized-moment signature cannot recover their level.
  regular-congruence-depth-mixtures-remain-folner: that treats SL3 conductor profiles and denominator shifts; this is an exact local-character blindness theorem for the SL2 BS14-Iwahori presentation.
  finite-covariance-mixed-words-remain-character-blind: that swaps two lamp characters inside one finite restriction fiber; this compares distinct congruence kernels using regular representations of the full arithmetic group.
---

Let `A=PSL_2(Z[1/2])`, and fix finitely many noncommutative normalized-trace
tests built from finitely many group words.  Equivalently, after expanding
products and adjoints, fix a finite subset

```text
F subset C[A].                                         (BML1)
```

There are arbitrarily deep, pairwise distinct odd prime congruence levels
`p,q` and exact representations of `A` of the **same dimension** which have
identical values on every test in `F`.

Indeed let `lambda_p` be the left regular representation of
`Q_p=PSL_2(F_p)`.  For every fixed finite set
`K subset A\{1}`, reduction modulo `p` is nontrivial on every element of
`K` for all but finitely many odd primes.  Hence, for sufficiently large
`p`,

```text
tr_(Q_p)(lambda_p(g))=0       (g in K),                (BML2)
```

and the normalized trace of every `a in F` is exactly its identity
coefficient.  Choose two such primes and amplify

```text
rho_p=lambda_p^(+|Q_q|),       rho_q=lambda_q^(+|Q_p|). (BML3)
```

Both have dimension `|Q_p||Q_q|`, all fixed moments agree exactly, but
their kernels and minimal congruence levels are different.

The same conclusion covers every fixed finite-support Hecke test: a finite
sum of fixed double-coset representatives and any prescribed finite list of
its products still expands into one finite subset of `C[A]`.  A central
idempotent belonging to the **moving** finite quotient can of course detect
that quotient, but its support and coefficients depend on the unknown
level; it is not a level-independent test.

All four BS14-Iwahori presentation residuals vanish identically in
`rho_p,rho_q`.  Therefore their cubic residual polar data are both the zero
datum and add no level information.  This rules out a level extractor based
only on a fixed finite collection of scalar word/Hecke moments and residual
energies.

There is also a same-level strengthening.  In
`cuspidal-redistribution-refutes-regular-core-orbit-basin`, the regular
representation `rho_p` and a cuspidally redistributed exact representation
`eta_p` have literally identical BS cores, and their normalized characters
both converge pointwise to the canonical character.  Thus every fixed finite
moment window differs by `o(1)`, while their endpoint orbits stay a fixed
normalized-HS distance apart.  Scalar moments therefore cannot select the
point of the restriction-ring fiber either, even after the level and core
have been authenticated.

The claim does not rule out an operator-valued, dimension-growing decoder
which uses the full spectral geometry of `(R,S,X)`, nor does flexible repair
need to recover the minimal level when two levels give nearby endpoints.
It does show that moving-level authentication cannot begin by assigning a
finite moment fingerprint to every congruence atom.  Any positive theorem
must either be level-agnostic, use tests whose complexity grows with the
candidate conductor, or recover an exact endpoint directly without naming
its level or its restriction-kernel coordinate.
