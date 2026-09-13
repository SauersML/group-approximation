---
rg: 2
id: heavy-eigenvalue-gives-determinant-counterexample
kind: claim
title: An integral self-adjoint matrix with an eigenvalue of multiplicity above n over its degree has an integral polynomial image with determinant below one
distinct_from:
  galois-invariance-implies-algebraic-eigenvalues: that gets algebraic eigenvalues from invariance of kernel dimensions under automorphisms of C; this gets algebraic eigenvalues, with a multiplicity bound, from Lück's determinant conjecture, and turns a failure into an explicit determinant violation
  finite-spectrum-integral-elements-obey-determinant: that proves Galois-equal rational masses when the spectrum is finite; this assumes nothing about the spectrum and bounds single atoms by the degree
  atomic-serre-measures-are-equal-weight-real-orbits: that characterizes purely atomic Serre-class measures; this is the group-ring consequence of the atom bound for arbitrary spectral measures
artifacts:
  - research/artifacts/determinant-spectral-atoms-2026-09-12.md
---

**ESTABLISHED** by `heavy-eigenvalue-determinant-counterexample-proof`
(artifact Corollary 2). Unreviewed.

Let `G` be any group, `A in M_n(Z[G])` self-adjoint, `lambda in R`, and
`m = dim_(N(G)) ker(r_A - lambda)`. If

```text
m  >  n / deg(lambda)          (for transcendental lambda: m > 0),
```

then some nonzero `Q in Z[x]` has `det_(N(G)) r_(Q(A)) < 1`, so `G` violates
Lück's determinant conjecture.

The polynomial is explicit. Take `N = deg(lambda) - 1` (any `N` with
`(N+1) m > n` when `lambda` is transcendental), `C = max(1, ||A||)` and
`w = m/n`, choose `H` with `(w(N+1) - 1) log H > log((N+1) C^N)`, and let `Q`
be a nonzero integer polynomial of degree at most `N` and height at most `H`
with `|Q(lambda)| <= (N+1) C^N H^(-N)` (box principle).

**Contrapositive: the determinant conjecture implies algebraic eigenvalues.**
If `G` satisfies the conjecture, every eigenvalue of every self-adjoint integral
matrix over `G` is algebraic and

```text
dim_(N(G)) ker(r_A - lambda) <= n / deg(lambda).
```

- This covers every sofic group through
  `determinant-conjecture-holds-for-sofic-groups`, with no second use of
  approximation. Thom (arXiv:math/0701294v3, Theorem 1.1) proves more for
  sofic groups: integral eigenvalues with equal conjugate multiplicities.
- The conjecture forces neither of those extras at the level of one spectral
  measure (artifact Section 4, `serre-class-atoms-obey-degree-bound`).
- Literature check, bounded to Thom 2007 and Lück arXiv:1901.00827v2
  Remark 4.2: this implication was not found there.
