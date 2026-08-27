---
rg: 2
id: kazhdan-projection-finite-target-calculus
kind: claim
title: The Kazhdan projection calculus in finite C-star targets
distinct_from:
  kazhdan-asymptotic-commutant-transport: That claim is the sequential matrix-coordinate transport theorem; this one is the single exact statement about one finite C-star target from which the ultraproduct proof of that theorem is read off.
  kazhdan-projection-not-in-l1: That claim locates the Kazhdan projection outside l^1 and explains why averaging fails on Banach targets; this one uses only its image inside a fixed finite C-star algebra, where no averaging is needed.
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
---

Credit: external review session (2026-08-15, unrefereed); proof audited by
this session.  The statement is the common engine behind the transport,
scaled-transport, and normal-Kazhdan theorems.

Let `A` be a finite unital C-star algebra (every isometry is unitary), let
`rho : H -> U(A)` be a homomorphism, and let `L <= H` have property (T).
The image `p_L in A` of the Kazhdan projection of `C*_max(L)` satisfies:

1. if `s L s^{-1} <= L` then `rho(s) p_L rho(s)^* = p_L`;
2. if `L` is normal in `H` then `p_L in rho(H)'`;
3. if `p_L = 1` then `rho(L) = 1`.

Norm matrix coronas and norm ultraproducts of matrix algebras are finite
by polar correction, so every corona representation is covered.

**Why this is the master lemma.**  Clause 1 in the ultraproduct
`prod_omega B(K_n)` IS the printed proof of the manuscript transport
theorem, and with weighted inner products `Tr(y^* x)/w_n` it gives the
scaled transport at every weight in one stroke: the dimension-normalized
and rank-normalized transports are literally the same statement.  Clause 2
gives a corner proof of the normal-Kazhdan obstruction shorter than the
moving-spectral-subspace argument: for `K` normal Kazhdan inside a
universally tracially invisible subgroup, `p = Phi(p_K)` is
ambient-central by clause 2, the complementary corner `q = 1 - p` is
nonzero if the representation is nontrivial on `K` by clause 3, the
corner's GNS trace has no `K`-fixed vectors because `qpq = 0`, so a
Kazhdan generator keeps a definite renormalized 2-norm distance from the
corner identity — contradicting universal tracial invisibility.  That is
a second, corner-level route to the established normal-Kazhdan claims; the
formalized finite-stage proofs remain the machine-checked ones.
