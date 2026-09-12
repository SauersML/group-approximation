---
rg: 2
id: finite-spectrum-integral-determinant-proof
kind: route
title: Spectral projections of an algebraic integral element lie in the group algebra, so Zalesskii makes their traces rational
target: finite-spectrum-integral-elements-obey-determinant
requires:
  - zalesskii-idempotent-trace-is-rational
---

Let `G` be a group and `A in M_n(Z[G])` self-adjoint with finite spectrum.
Right multiplication `M_n(C[G]) -> B(l^2(G)^n)` is injective: evaluate at
`delta_e` vectors.

**Step 1: minimal polynomial in `Z[x]`.**

- **Annihilation.** Since `A` is self-adjoint with finite spectrum,
  `A = sum_lambda lambda E_lambda`, so `m(x) = prod_(lambda in sigma(A)) (x - lambda)`
  satisfies `m(A) = 0` in `B(l^2(G)^n)`, hence in `M_n(C[G])`.
- **`m` is the minimal polynomial.** By the spectral mapping theorem every
  annihilating polynomial vanishes on `sigma(A)`.
- **Rational coefficients.** The map `C[x]_(<= N) -> M_n(C[G])`,
  `p -> p(A)`, is linear with rational matrix entries. Its kernel therefore has
  a rational basis, so the annihilator ideal is defined over `Q` and `m in Q[x]`.
- **Integrality.** Let `k = deg m` and let `S` be the union of the supports of
  `I, A, ..., A^(k-1)`. Every `A^j` is a rational combination of these, so it
  is supported in `S`, and
  `Z[A] <= M_n(Z[G]) cap M_n(Q[S]) = M_n(Z[S])`,
  a free abelian group of finite rank.
  - So `Z[A]` is a finitely generated `Z`-module.
  - So `A` is integral: `h(A) = 0` for some monic `h in Z[x]`.
  - `m` divides `h`, so `m in Z[x]` by Gauss's lemma.
- **Conclusion.** `sigma(A)` is a Galois-stable set of real algebraic integers,
  hence totally real.

**Step 2: spectral projections are algebraic.** Put `K = Q(sigma(A))`, the
splitting field of `m`. For `lambda in sigma(A)` let

```text
p_lambda(x) = prod_(mu in sigma(A), mu != lambda) (x - mu)/(lambda - mu)  in K[x].
```

Then `p_lambda(A) = sum_nu p_lambda(nu) E_nu = E_lambda`. So the spectral
projection `E_lambda` is an idempotent of `M_n(K[G])`, and
`mu_A({lambda}) = Tr(E_lambda) = sum_i (E_lambda)_ii(1)`.

**Step 3: the masses are rational.** For `n = 1` this is
`zalesskii-idempotent-trace-is-rational`. For general `n`:

- **The embedding.** Let `F = S_(n+1)`. Its standard representation is
  absolutely irreducible of degree `n` and defined over `Q`, so `Q[F]` has a
  Wedderburn component `Q[F] c ~= M_n(Q)`, with `c` central. This gives a
  non-unital algebra embedding `iota: M_n(K) -> K[F]`.
- **Trace scaling on `F`.** The canonical trace is
  `tr_F(x) = x(1) = Tr_reg(x)/|F|`. The regular representation contains the
  standard one `n` times, so `tr_F(iota(X)) = (n/|F|) Tr(X)` for
  `X in M_n(K)`.
- **Tensoring with `K[G]`.** `iota_G = iota (x) id`:
  `M_n(K) (x) K[G] -> K[F] (x) K[G] = K[F x G]` is an algebra homomorphism.
  Since `tr_(F x G)(x (x) y) = tr_F(x) tr_G(y)` and
  `tr_F(iota(E_ij)) = (n/|F|) delta_ij`,

  ```text
  tr_(F x G)(iota_G(Y)) = (n/(n+1)!) sum_i tr_G(Y_ii).
  ```
- **Conclusion.** `iota_G(E_lambda)` is an idempotent of `K[F x G]`. Zalesskii
  makes its trace rational, so `Tr(E_lambda)` is rational.

**Step 4: conjugates carry equal mass.**

- Write `p_lambda(x) = sum_j c_j(lambda) x^j`. Then
  `Tr(E_lambda) = sum_j c_j(lambda) Tr(A^j)`, and every `Tr(A^j)` is an
  integer.
- Each `sigma in Gal(K/Q)` permutes `sigma(A)`. The coefficients `c_j(lambda)`
  are rational functions of the roots, so `sigma(c_j(lambda)) = c_j(sigma lambda)`.
- Hence `sigma(Tr(E_lambda)) = Tr(E_(sigma lambda))`. By Step 3 the left side
  equals `Tr(E_lambda)`.

**Step 5: Serre inequalities and determinants.**

- **Orbits.** Split `sigma(A)` into Galois orbits `O`, the root sets of monic
  irreducible factors `f_O in Z[x]` of `m`, each carrying one common mass
  `w_O`. A nonzero `Q in Z[x]` vanishes at one point of `O` if and only if it
  vanishes at all of them.
- **Each orbit contributes nonnegatively.** On an orbit where `Q` does not
  vanish, the orbit contributes `w_O log |prod_(lambda in O) Q(lambda)|`. That
  product is the norm of the nonzero algebraic integer `Q(lambda)`, a nonzero
  rational integer, so the contribution is `>= 0`.
- **Determinants.** For `B` with `A = B^* B` of finite spectrum,
  `log det_N(G)(B) = (1/2) integral_{x != 0} log |x| d mu_A >= 0`, which is the
  case `Q = x`.

No property of `G` was used. Soficity enters the known proofs only to handle
elements that are not algebraic.
