---
rg: 2
id: thompson-t-pentagon-winding-sandwich-proof
kind: route
title: Conjugate r_1 to its inverse by the involution a^2, lift the relators to the line for the Euler pairing, and transport Dadarlat's nonzero commutator winding to (BA)^60 along a path of tuples
target: thompson-t-pentagon-winding-sandwich
requires:
  - thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
  - thompson-t-lochak-schneps-presentation
  - dadarlat-linear-groups-have-nonzero-h2-windings
  - thompson-v-has-haagerup-property
artifacts:
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/euler_pairing.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/out_euler_pairing.json
---

Numbering follows the claim. In this proof a *pair* means an exact pair: `A^4 = B^3 = 1`.

For a unitary `U` whose spectrum avoids `-1`, put `kappa(U) = (1/2 pi i) Tr log U` (principal branch).
Then `exp(2 pi i kappa(U)) = det U`, and `kappa` is invariant under conjugation.

## (1) Quantisation

`det A` lies in `mu_4` and `det B` in `mu_3`, so `det((BA)^5)` lies in `mu_12`. Therefore
`kappa_P` lies in `(1/12) Z`. A commutator has determinant 1, so `kappa(r_2(A,B))` lies in `Z`.

## (2) The r_1-winding vanishes

`J = A^2` satisfies `J^2 = 1`. The words `X = bab` and `a^2 bab a^2` are palindromes, so under either
reading convention they evaluate to `X = BAB` and `Y = JXJ`. The relator `r_1` evaluates to
`U = [X,Y] = XYX^(-1)Y^(-1)` under one convention and to `U' = Y^(-1)X^(-1)YX` under the other. Since
`JXJ = Y` and `JYJ = X`:
- `J U J = [Y, X] = U^(-1)`;
- `J U' J = X^(-1) Y^(-1) X Y = U'^(-1)`.

For the principal branch, `log(U^(-1)) = -log U` when `-1` is not in the spectrum. Hence
`kappa(U) = kappa(JUJ) = kappa(U^(-1)) = -kappa(U)`, so `kappa(U) = 0`, and likewise for `U'`.

## (3) The Euler class `x_0`

Let `T-bar` be the group of lifts of elements of `T` to homeomorphisms of `R` commuting with
`x -> x + 1`. Its kernel over `T` is the integer translations, which are central. Fix lifts
`alpha-bar(x) = x + 1/4` and `beta-bar`, with `beta-bar(0) = 1/2`.

For `c` in `N ∩ [F,F]`, the element `c(alpha-bar, beta-bar)` lifts the identity, so it is a translation
by an integer `e(c)`.
- **Independence of the lifts.** Changing a lift by a central translation changes `e(c)` by a multiple
  of the exponent sum of that generator in `c`. That sum is 0, because `c` lies in `[F,F]`.
- **A homomorphism.** `e` is additive, since the values are central.
- **It vanishes on `[N,F]`.** For `n` in `N`, the element `n(alpha-bar, beta-bar)` is central, so
  `[n, f]` evaluates to 1.

So `e` descends to a homomorphism `H_2(T;Z) = (N ∩ [F,F])/[N,F] -> Z` (Hopf). This uses only the true
kernel `N`, not the presentation.

The relators `a^4`, `b^3` and `r_P` lie in `N` (`verify_ls.py`), so each evaluates on the lifts to an
integer translation, which is read off at one point. `euler_pairing.py` does this in exact arithmetic
and writes `out_euler_pairing.json`:
- `e(a^4) = 1`, `e(b^3) = 1`, `e(r_1) = e(r_2) = 0`, `e((ba)^5) = 3`.
- The exponent sums of `c_0 = r_P^12 (a^4)^(-15) (b^3)^(-20)` are `12*5 - 15*4 = 0` in `a` and
  `12*5 - 20*3 = 0` in `b`, so `c_0` lies in `[F,F]`.
- Hence `e(x_0) = 12*3 - 15 - 20 = 1`, and `x_0` is non-torsion.

For a pair, `c_0(A,B)` is `(BA)^60 A^(-60) B^(-60) = (BA)^60`, or `(AB)^60` under the other reading.
These are conjugate, so they have the same `kappa`.

## (4) The sandwich

**First arrow: `T` not MF implies (PW).** By `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`
item (3), there is `epsilon_0 > 0` such that every `epsilon_0`-pair is `(1,1)`. For such a pair
`(BA)^5 = 1`, so `kappa_P = 0`. So (PW) holds with `delta = epsilon_0`.

**Second arrow: (PW) implies `T` is not quasidiagonal.** Suppose that `T` is a quasidiagonal group.

*Step 1: Dadarlat's hypotheses hold.*
- `T <= V` has the Haagerup property (`thompson-v-has-haagerup-property`). A proper conditionally
  negative definite function gives a coarse embedding into Hilbert space.
- Dadarlat, arXiv:2111.05755, p. 7, verbatim from the primary text (the same fetch as
  `dadarlat-linear-groups-have-nonzero-h2-windings-citation`): "The groups which are coarsely
  embeddable in a Hilbert space admit a γ-element, [27]."
- Since `c_0` lies in `[F,F]`, write `c_0 = prod_{i=1}^g [a_i, b_i]` in `F`. Its image in `T` is 1,
  and its Hopf class is `x_0`, which is non-torsion by (3).

*Step 2: Theorem 3.2.* Theorem 3.2 (quoted in `dadarlat-linear-groups-have-nonzero-h2-windings`)
gives a unital asymptotic homomorphism `pi_n : T -> U(k_n)` with
`wn det((1-t) + t P_n) != 0` for large `n`, where `P_n = prod [pi_n(a-bar_i), pi_n(b-bar_i)]`.
- Asymptotic multiplicativity gives `||P_n - 1|| -> 0`, because `pi_n(1) = 1`.
- So for large `n`, Lemma 2.1 there identifies that winding number with `kappa(P_n)`, and
  `kappa(P_n) != 0`.

*Step 3: exact pairs.* Put `u_n = pi_n(alpha)` and `v_n = pi_n(beta)`.
- For every word `w`, asymptotic multiplicativity gives `||w(u_n, v_n) - pi_n(w-bar)|| -> 0`.
- Hence `||u_n^4 - 1||` and `||v_n^3 - 1||` tend to 0. Spectral rounding (L0b of the criterion's proof)
  gives exact `A_n`, `B_n` with `||A_n - u_n||` and `||B_n - v_n||` tending to 0.
- Since `r_1, r_2, r_P` lie in `N`, `D(A_n, B_n) -> 0`.

*Step 4: transport of the winding, uniformly in dimension.* Put `x_i^0 = pi_n(a-bar_i)` and
`x_i^1 = a_i(A_n, B_n)`, and similarly `y_i^0`, `y_i^1` for `b_i`.
- Then `||x_i^0 - x_i^1||` and `||y_i^0 - y_i^1||` tend to 0.
- Join them by `x_i^s = x_i^0 exp(s log((x_i^0)^(-1) x_i^1))`, and similarly for `y_i^s`.
- `P(s) = prod [x_i^s, y_i^s]` is a continuous path **in `SU(k_n)`**, because commutators have
  determinant 1.
- It stays within `||P_n - 1|| + o(1) < 2` of 1. So `kappa(P(s))` is continuous and integer-valued,
  hence constant.

Therefore `kappa(c_0(A_n, B_n)) = kappa(P(1)) = kappa(P(0)) != 0`.

This path argument is needed. `kappa` is **not** uniformly continuous across dimensions: in dimension
`k`, `e^(2 pi i/k) 1_k` lies in `SU(k)`, is within `2 pi/k` of 1, and has `kappa = 1`. The argument
works only because the path stays in `SU`.

*Step 5: from 60 to 5.* For large `n`, `||(B_n A_n)^5 - 1|| < 2 sin(pi/24)`. Then every eigenvalue of
`(BA)^5` has angle in `(-pi/12, pi/12)`, and the functional calculus gives
`log((BA)^60) = 12 log((BA)^5)`. So `kappa_P(A_n, B_n) = kappa((B_n A_n)^60)/12 != 0`, while
`D(A_n, B_n) -> 0`.

This contradicts (PW). The contrapositive of the first arrow gives the equivalent form: such a sequence
makes `delta_n -> 0`, and then `T` is MF by the criterion.

## (5) Delta(4,3,5)

`1/4 + 1/3 + 1/5 < 1`, so `Delta(4,3,5)` is a cocompact Fuchsian group. It is finitely generated and
linear (`PSL(2,R) ≅ SO^+(2,1)`). Dadarlat's sentence after Theorem 3.2 (quoted in
`dadarlat-linear-groups-have-nonzero-h2-windings`) gives the hypotheses of Theorem 3.2.

`alpha, beta` satisfy the relators of `Delta` in `T`, so there is a homomorphism `phi : Delta -> T`.
The word `c_0` lies in `ker(F -> Delta) ∩ [F,F]`, and Hopf's formula is natural, so
`phi_*[c_0]_Delta = x_0`. By (3), `[c_0]_Delta` is non-torsion.

Steps 2 to 5 use only that `a^4`, `b^3` and `(ba)^5` are killed. So they give pairs with
`||(B_n A_n)^5 - 1|| -> 0` and `kappa_P != 0`.

## (6) Windings cancel

`kappa_P(A-bar, B-bar)` is the complex conjugate of `kappa_P(A, B)`, which is `-kappa_P(A, B)` because
`kappa_P` is real. Also `D(A-bar, B-bar) = D(A, B)`. Defect and winding both behave additively under
direct sums, in the sense that the defect is the maximum and the winding is the sum.

## What was checked and what was not

- **Imported.**
  - Dadarlat's Theorem 3.2, its Lemma 2.1, and the gamma-element sentence were read from the primary
    text.
  - The standard implication "Haagerup implies coarse embeddability" is used.
  - The first arrow uses the criterion, and so uses completeness of the Lochak--Schneps presentation.
- **Not needed.** The second arrow and (5) use only relators that hold in `T`, which is verified.
- **Exact computation.** The Euler numbers were computed exactly.
- **Not Lean-verified.**
