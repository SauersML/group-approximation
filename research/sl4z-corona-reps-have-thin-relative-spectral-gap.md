---
rg: 2
id: sl4z-corona-reps-have-thin-relative-spectral-gap
kind: claim
title: In every matrix corona representation of SL_4(Z), vectors invariant under the thin subgroup are invariant under the lattice
artifacts:
  - research/artifacts/sl4z-thin-corona-gap-reduction-2026-09-16.md
distinct_from:
  sl4z-corona-representations-have-block-sl2-norm-four: that asks the block SL_2(Z) Laplacian to have norm four in every corona representation, which fails on MF models of the reduced algebra and holds on the full algebra; this asks for a relative spectral gap for the thin subgroup C, which holds on MF models of the reduced algebra and fails on faithful representations of the full algebra.
  thin-sln-robust-relative-commutant-transfer: that is a normalized Hilbert--Schmidt transfer modulus for commutants under Hilbert--Schmidt relator defect, aimed at hyperlinearity; this is an operator-norm corona statement about single vectors, aimed at MF, and implies only the operator-norm-hypothesis case of that modulus.
  thin-selected-fd-null-cutoff-cannot-survive-matrices: that asks one finite-dimensional-null sequence to die on a selected tracial-ultraproduct unitary; this asks the single element x = mu(1-p) to keep norm below one in operator-norm matrix coronas.
  fd-mark-stability-forces-mf-invisibility: that derives MF invisibility of a marked group element from stability at that element; this is a spectral inequality for a positive element of C*(SL_4(Z)), with no correction of lifts assumed.
---

Let `Gamma = SL_4(Z)`, and let `C`, `F`, `S`, `p`, `mu` and `x = mu(1 - p)` be as in
`sln-z-thin-quasiregular-not-weakly-contained-in-fd`.  Write
`Q_k = prod_n M_(k_n) / sum_n M_(k_n)`.

**Claim (C).**  Every unital *-homomorphism `pi : C*(Gamma) -> Q_k`, for every sequence
`k`, satisfies

```text
||pi(x)|| < 1.
```

The artifact (Section 8) proves the following equivalent forms.

1. **Fixed vectors.**  For every such `pi` and every representation of `Q_k` on a Hilbert
   space, the `C`-invariant vectors are `Gamma`-invariant.
2. **Linear modulus.**  There is `t < 1` such that, in every Hilbert space realization of
   every such `pi`,

   ```text
   (1 - t) ||(1 - pi(p)) xi||^2 <= (1/32) sum_(c in F) ||pi(c) xi - xi||^2.
   ```

   Uniformity in `pi` is automatic (Corollary 8.5).
3. **Finite robust form.**  For every `eta > 0` there are a finite `E` in `Gamma` and
   `delta > 0` such that, for every `k`, every `phi : Gamma -> U(k)` with operator-norm
   defect `< delta` on `E`, and every unit `v in C^k`,

   ```text
   sum_(c in F) ||phi(c) v - v||^2 < delta   implies   sum_(s in S) ||phi(s) v - v||^2 < eta.
   ```

   It suffices to have this for one `eta < kappa_S^2`, the Kazhdan constant of `S`.

**Why it matters.**
- It follows from `sl4z-matricially-stable`, with the explicit bound `1 - epsilon`
  (route `sl4z-thin-gap-from-matricial-stability`).
- It implies `sl4z-full-cstar-is-not-mf`, and also that `C*_(sigma_C)(SL_4(Z))` is not MF
  (route `sl4z-full-not-mf-from-thin-corona-gap`).
- **Refutation criterion.**  Any corona representation with `||pi(x)|| = 1` refutes (C),
  and hence refutes point-norm matricial stability of `SL_4(Z)`.  For example, an MF model
  of `C*(SL_4(Z))`, or of its image in the thin quasi-regular representation, would do.

**Where it is known to hold.**
- On corona representations of product form `q o (rho_n)` with genuine
  finite-dimensional `rho_n`.
- In particular on MF embeddings of `C*_r(SL_4(Z))`, since `lambda` is weakly contained in
  the finite-dimensional representations.

**Where the analogous statement fails.**  It fails for the genuine representation
`sigma_C` on `l^2(Gamma/C)`.  So no inequality valid in all unitary representations can
prove it: a proof must use matrix origin.

## Attempts

- **Correct the lifts.**  Point-norm matricial stability of `SL_4(Z)` gives (C) at once.
  But that is the open target itself, and no weaker correction statement is known that
  suffices.
- **Use the free restriction.**  Free groups are matricially stable, so
  `pi|_C = q o (psi_n)` for genuine representations `psi_n` of `C`.
  - Genuine representations of a free group can have almost invariant vectors.
  - The Bourgain--Varju gap is available only for representations that factor through
    congruence quotients, and a corona representation factors through no finite quotient.
  - So the gap cannot be imported without controlling how the correction on `C` interacts
    with the rest of `Gamma`.
- **Round permutation models.**  Operator-norm asymptotic homomorphisms by permutation
  matrices are eventually genuine finite actions, since distinct permutation matrices are
  at distance at least `sqrt(2)`.
  - They factor through congruence quotients, where `C` is co-dense, so they satisfy (C).
  - So permutation rounding can neither refute (C) nor exhibit the thin coset action in a
    corona.
- **Sum-of-squares certificate in `C*(Gamma)`.**  Impossible, since `sigma_C` violates the
  inequality.
- **Traces.**  Normalized traces cannot decide (C).  A failure of (C) needs only a sequence
  of single top eigenvectors of lifts `X_n` of `pi(x)`, and a normalized trace gives such
  vectors weight `1/k_n`.
  - Bekka (Invent. Math. 169 (2007), arXiv:math/0609102) gives, per its abstract, "a
    complete description of the tracial states on the full C*-algebra of Gamma".  The
    description itself was not re-read.
  - If every trace on `C*(SL_4(Z))` is a limit of finite-dimensional traces, as that
    description is usually recorded, then the spectral projection of `X_n` onto
    `[1 - epsilon + eta, 1]` has normalized rank tending to `0`.
  - So any failure of (C) is tracially invisible.  This lane did not verify the
    classification, and nothing here depends on it.
- **Hilbert--Schmidt transfer.**
  - The adjoint trick (artifact, Proposition 9.1) shows that (C) implies the
    operator-norm-hypothesis case of `(TRC1)` in
    `thin-sln-robust-relative-commutant-transfer`.
  - `(TRC1)` concerns trace-weighted vectors of the conjugation module and does not
    obviously give (C).
