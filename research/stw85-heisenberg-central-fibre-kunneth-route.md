---
rg: 2
id: stw85-heisenberg-central-fibre-kunneth-route
kind: route
title: Specialize the central character and run graded Kunneth with the exterior-exponential trace
target: stw85-integral-heisenberg-ktu-is-explicit
requires:
  - stw85-integral-heisenberg-irrep-quotients-are-torus-powers
artifacts:
  - research/artifacts/stw85-integral-heisenberg-invariant-audit-2026-08-31.md
---

Schur's lemma makes the central generator scalar.  Specializing it at
`exp(2 pi i theta)` turns the `n` commuting Heisenberg pairs into
`n` commuting copies of `A_theta`.  Nuclearity identifies their
maximal universal tensor product with `A_theta^(tensor n)`.

For irrational `theta`, the block skew form
`Theta_(n,theta)` is nondegenerate.  The resulting noncommutative torus
is simple and uniquely tracial, so the irreducible representation is
faithful.  For rational `theta=p/q`, the central unitaries
`U_j^q,V_j^q` become scalars in an irreducible representation; after
normalization each pair is the q-dimensional clock--shift algebra.
Their tensor product is `M_(q^n)`.  Taking determinants in
`V_jU_j=exp(2 pi i theta)U_jV_j` proves the converse finite-dimensional
implication.

Pimsner--Voiculescu gives two free even and two free odd generators for
one factor.  The graded Kunneth theorem therefore has no Tor terms, and
its parity split gives

```text
rank K_0=rank K_1=(4^n)/2=2^(2n-1).
```

Under the exterior-algebra identification, Elliott's trace formula is

```text
exp_wedge(Theta_(n,theta))
 =product_(j=1)^n(1+theta a_j wedge b_j),
```

which is precisely (H85-3).  Phillips' simple-real-rank-zero theorem and
trace comparison determine (H85-4).  The coefficient exact sequence
splits without Tor because both integral K-groups are free, proving
(H85-5).  No classification or uniqueness of the individual irreducible
Hilbert-space representations is used.
