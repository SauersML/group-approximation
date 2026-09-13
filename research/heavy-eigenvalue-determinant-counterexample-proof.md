---
rg: 2
id: heavy-eigenvalue-determinant-counterexample-proof
kind: route
title: A heavy eigenvalue is a heavy atom of the normalized spectral measure, so the box-principle polynomial has negative log determinant
target: heavy-eigenvalue-gives-determinant-counterexample
requires:
  - serre-class-atoms-obey-degree-bound
  - determinant-conjecture-iff-serre-class-spectra
artifacts:
  - research/artifacts/determinant-spectral-atoms-2026-09-12.md
  - research/artifacts/determinant-conjecture-serre-class-2026-09-11.md
---

Artifact Section 3.

1. **The atom.** For the normalized trace `(1/n) Tr (x) tau`, the spectral
   measure `mu_A` has `mu_A({lambda}) = m/n = w`, and `w > 1/deg(lambda)`.
2. **Negative integral.** Step 4 of `serre-class-atoms-degree-bound-proof` at
   `x = lambda`, with `H` as in the claim, gives
   `integral_(Q != 0) log|Q| d mu_A < 0` for the box-principle polynomial `Q`.
3. **Functional calculus.** `Q(A)` is a self-adjoint element of `M_n(Z[G])`,
   and ([SC] Section 0, identity (FC); the kernel is excluded by the
   Fuglede--Kadison convention)

   ```text
   log det_(N(G)) r_(Q(A)) = n * integral_(Q != 0) log|Q| d mu_A < 0.
   ```

4. **Contrapositive.** If `G` satisfies the conjecture, every `mu_A` is in
   the Serre class (`determinant-conjecture-iff-serre-class-spectra`), and
   `serre-class-atoms-obey-degree-bound` gives `m <= n / deg(lambda)`. QED
