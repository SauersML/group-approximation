---
rg: 2
id: leavitt-invisible-half-universal-over-every-finite-field-proof
kind: route
title: Scalar-free constants with a representation-killed idempotent cut the scalar copy into the kernel
target: leavitt-invisible-half-universal-over-every-finite-field
requires: []
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/leavitt-invisible-corner-transfer-2026-09-12.md
---

Sections "General criterion" (Theorem 6) and "Existence over every finite field" (Lemma 7,
Propositions 8 and 9, Corollary 10) of the artifact.

1. `Theta_n` is a unital ring isomorphism, by (M1) and (M2) on words of length `k`.
   `delta_n(Q)` commutes with `Theta_n(H)` because `F` is central. They meet only in `1`: an
   equality `delta_n(q) = Theta_n(h)` forces `h = q I_n`, and `H` has no nontrivial scalars.
   So `J : S (x)_F F[H] -> S` is an injective ring homomorphism.
2. `z = J(1 (x) e)` has `pi(z) = Theta_n(rho_n(e)) = 0`.
3. `mu(a) = J(a (x) e)` is multiplicative with `mu(1) = z` and image in `zSz`. It is injective
   because `a (x) e != 0` for `a != 0` over a field, and `J` is injective.
4. Pairs pad by `1 - z`. The reverse implications are the unital inclusions `K^+ <= S` and
   `(1 - z) + zSz <= S`.
5. Existence:
   * `d = 2`, `q != 3`: diagonal or non-split torus elements of odd prime order dividing
     `q +- 1`.
   * `d >= 3`: Zsigmondy primitive prime divisors of `q^d - 1`, citing Zsigmondy (1892) as a
     classical theorem, with blocks for `(2, 6)`.
   * `(3, 2)`: the level-two Klein group, after Proposition 9 shows level one is empty.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 18 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
