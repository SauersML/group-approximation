---
rg: 2
id: profinite-kernel-fixed-dimension-hs-bound-proof
kind: route
title: Krull intersection on the universal representation puts the word in the relator ideal, and evaluation on unitaries is linear
target: profinite-kernel-words-have-fixed-dimension-hs-bounds
requires: []
artifacts:
  - research/artifacts/thompson-f-fixed-dimension-hs-bounds-2026-09-16.md
---

Full proofs: artifact, Sections 1 and 2 (Theorem 1.1, Theorem 1.3, Propositions 2.1--2.3, Corollary 2.4). Numbering
follows the claim.

**1. Ideal membership.** Put `A = B_0/J_n(R)` and let `xi_s` be the image of `X_s`.
- `X_s adj(X_s) = det(X_s) I`, so `xi_s` is invertible, and `s -> xi_s` gives `rho : P -> GL_n(A)`. For each word,
  `rho(g)` is the image of `g(X)`.
- Suppose an entry `e` of `rho(w) - I` is nonzero. `A` is Noetherian (Hilbert basis theorem). Choose a maximal
  `m ⊇ Ann(e)`. Then `e/1 != 0` in `A_m`, and Krull's intersection theorem in the Noetherian local ring `A_m` gives
  `k` with `e notin m^k`.
- `A/m` is a field that is finitely generated as a ring, hence finite. In characteristic `p` use Zariski's lemma. In
  characteristic zero, Zariski and Artin--Tate would make `Q` a finitely generated `Z`-algebra, which it is not. Each
  `m^i/m^(i+1)` is a finite-dimensional `A/m`-space, so `A/m^k` is finite.
- `P -> GL_n(A/m^k)` is a homomorphism to a finite group that does not kill `w`. This contradicts profinite triviality.

**2. Linear bound.** Item 1 gives integer polynomials with
`(w(X) - I)_(ab) = sum_(r,k,l) p_(r,kl)^(ab) (r(X) - I)_(kl) + sum_s q_s^(ab) (y_s det X_s - 1)`. Substitute
`x_(s,ij) = (U_s)_(ij)` and `y_s = conj(det U_s)`. The last sum vanishes, every variable has modulus at most `1`, so
`|p(U)| <= L_n`. Cauchy--Schwarz gives `sum_(kl) |M_(kl)| <= n^(3/2) ||M||_2`. Hence
`|(w(U) - I)_(ab)| <= |R| n^(3/2) L_n delta_R(U)`, and `||M||_2 <= n^(1/2) max |M_(ab)|` gives the bound.

**3. Converse.** If `pi : P -> Q` is onto a finite group, the permutation matrices of the left regular representation of
`Q` give a tuple with `delta_R = 0`. Finiteness of `C_|Q|` forces `w` to act trivially, and the regular representation is
faithful, so `pi(w) = 1`. The other direction is item 2.

**4. Monotone.** `U -> U ⊕ 1` multiplies every `||g(U) - I||_2^2` by `n/(n+1)` and leaves all ratios unchanged.

**5. Mass form.** Split `U = ⊕ U^(i)` into irreducible blocks, so `e_U(g) = sum_i (n_i/n) e_(U^(i))(g)`. For `n_i <= D`
use item 4 and `delta_R^2 <= sum_r e(r)` to get `e_(U^(i))(w) <= C_D^2 sum_r e_(U^(i))(r)`. For larger blocks use `e <= 4`.
Then sum, using `sum_r e_U(r) <= |R| delta_R(U)^2`.

**6. Projective form.** `g(U ⊗ conj U) = g(U) ⊗ conj g(U)` has normalized trace `|tr g(U)|^2`, so its `e`-value is
`2 (1 - |tr g(U)|^2)`. Apply item 2 in dimension `n^2`.
