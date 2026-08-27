---
rg: 2
id: finite-phase-codewords-weight-type-gram-leakage
kind: claim
title: Finite phase codewords give an error-correcting fingerprint for type-Gram leakage
distinct_from:
  finite-phase-monomial-game-algebra-dictionary: that resolves the powers of each quantum-reflection entry into phase projections; this assigns several independent spectral tags to an already decoded finite type partition and quantifies their separation.
  bounded-type-balanced-occurrences-synchronize: that synchronizes bounded representation types by empirical rounding; this gives an exact word-energy weight for cross-type Gram blocks without aligning multiplicities.
---

Let `(Q_omega)_(omega in Omega)` be a finite orthogonal partition and assign
distinct codewords

```text
c(omega) in (Z/m)^t
```

of minimum Hamming distance `h`.  Define

```text
D_l=sum_omega zeta^(c_l(omega))Q_omega,       1<=l<=t.
```

For every unitary `P`, the sum of the Fourier normalizer energies of all
`D_l` charges each cross-type block according to the code coordinates on
which its endpoint types differ.  In particular,

```text
sum_(omega!=nu,rho)
 ||Q_omega P Q_rho (Q_nu P Q_rho)^*||_2^2
 <=1/(4mh sin^2(pi/m))
   sum_(l=1)^t sum_(r=1)^(m-1)
   ||[P D_l^r P^*,D_l]_add||_2^2.                     (PCG1)
```

Thus arbitrary multiplicities are harmless once the type projections are
authenticated: a finite error-correcting phase fingerprint turns every
cross-type Gram leak into ordinary commutator-word energy.
