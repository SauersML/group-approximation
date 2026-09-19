---
rg: 2
id: thompson-t-mf-iff-opnorm-z4-z3-defect-gap-proof
kind: route
title: Round each cyclic generator's spectrum to roots of unity, use that the Lochak--Schneps relators hold in T, and read off nontriviality from the rounded generators
target: thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
requires:
  - thompson-t-lochak-schneps-presentation
  - countable-group-mf-conventions
artifacts:
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/verify_ls.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/find_words.py
---

Numbering follows the claim. `||.||` is the operator norm.

**MF convention.** This is the one used in `thompson-v-mf-iff-opnorm-s4-s3-defect-gap-proof`. For a
filter `F` on `N` (Frechet, or a free ultrafilter) and dimensions `d_m`, let
`U_F = prod_m U(d_m) / {(u_m) : lim_F ||u_m - 1|| = 0}`. A group is MF iff it embeds in some `U_F`;
`countable-group-mf-conventions` identifies this with the C*-corona definition. `Rad_MF(T)` is the
intersection of the kernels of all homomorphisms `T -> U_F`. "`T` has full MF radical" means that every
such homomorphism is trivial.

`T` is simple (Cannon--Floyd--Parry 1996, Thm 5.8, as cited in `thompson-t-has-full-mf-radical`). So
"not MF" and "full MF radical" are the same statement.

## L0. Three elementary facts

**(L0a) Words are Lipschitz.** If `||x_j - y_j|| <= eta` for unitaries, then a word of length `l`
satisfies `||w(x) - w(y)|| <= l eta`.

**(L0b) Spectral rounding.** Let `u` be unitary and `k >= 2`. Let `f(u) = sum_zeta zeta E_zeta`, where
`E_zeta` is the spectral projection of `u` for the eigenvalues whose nearest `k`-th root of unity is
`zeta` (ties broken by a fixed rule). Then `f(u)^k = 1` and `||f(u) - u|| <= (pi/2k) ||u^k - 1||`.

*Proof.* Take an eigenvalue `lambda` at arc distance `theta <= pi/k` from its nearest root `zeta`. Then
`|lambda^k - 1| = 2 sin(k theta/2) >= 2k theta/pi` by Jordan's inequality, since `k theta/2 <= pi/2`.
Hence `|lambda - zeta| <= theta <= (pi/2k) |lambda^k - 1| <= (pi/2k) ||u^k - 1||`. The difference
`f(u) - u` is normal, so its norm is the largest such `|lambda - zeta|`.

**(L0c) Exact nontriviality is uniform.** If `A^4 = 1` and `A != 1`, then `A` has an eigenvalue in
`{i, -1, -i}`, so `||A - 1|| >= sqrt 2`. If `B^3 = 1` and `B != 1`, then `||B - 1|| >= sqrt 3`.

## L1. Structure of `delta_n`: (1), (2), (4), (5)

**Direct sums.** Words are evaluated blockwise, so `D(rho_1 (+) rho_2) = max D(rho_i)`, and
`D(1,1) = 0`.
- Padding a nontrivial pair by `(1,1)` gives `delta_(n+1) <= delta_n`.
- A nontrivial `rho` has a nontrivial irreducible summand `sigma` with `D(sigma) <= D(rho)`, and
  conversely `sigma (+) 1` realises `D(sigma)`. This is (2).

**Normal form (4).** Conjugate `A` to a fixed diagonal matrix. The centraliser of `A` then acts on `B`,
but it suffices that `B = Y B_0 Y^*` with `Y` in `U(n)`, where `B_0` is diagonal with the same
multiplicities. Finitely many multiplicity vectors occur.

**Compactness.** By (L0c), the nontrivial pairs form a closed subset of that compact set, so `delta_n` is
attained.

**Positivity.** A minimiser with `D = 0` would be a nontrivial homomorphism
`G0 / <<r_1, r_2, r_P>> -> U(n)`. By `thompson-t-lochak-schneps-presentation`, the source is `T`. Because `T`
is simple, the image of that homomorphism is isomorphic to `T`. It is a finitely generated linear group,
so it is residually finite (Malcev). An infinite simple group is not residually finite, so this is a
contradiction, and `delta_n > 0`.

**`delta_1`.** For `A = i^k` and `B = w^l`, where `w = e^(2 pi i/3)`, the commutators are 1, and
`(BA)^5 = w^(2l) i^k`. The map `(k,l) -> w^(2l) i^k` is a bijection `Z/4 x Z/3 -> mu_12`. So a nontrivial
pair has `(BA)^5` a nontrivial 12th root of unity, and `delta_1 = |e^(2 pi i/12) - 1| = 2 sin(pi/12)`.

**Arithmetic form (5).** "Some nontrivial `(A,B)` in `U(n)^2` has `A^4 = B^3 = 1` and `D < q`" is
first-order over the reals with rational coefficients. The operator-norm conditions are written as
positive definiteness of `q^2 - (r - 1)^*(r - 1)`, and nontriviality as `A != 1 or B != 1`.
Tarski--Seidenberg decides it.

## L2. A nontrivial homomorphism `T -> U_F` gives `delta_n -> 0`

Let `theta : T -> U_F` be any **nontrivial** homomorphism. Injectivity is not needed.
- **Lifts.** Choose lifts `(a_m)`, `(b_m)` of `theta(alpha)`, `theta(beta)`.
- **Small relator defect.** The five relators hold in `T`. This is the verified half of
  `thompson-t-lochak-schneps-presentation` (`verify_ls.py`). So
  `lim_F ||a_m^4 - 1|| = lim_F ||b_m^3 - 1|| = 0`, and likewise `lim_F ||r(a_m, b_m) - 1|| = 0` for
  `r = r_1, r_2, r_P`.
- **Exact pairs.** Put `A_m = f(a_m)` and `B_m = f(b_m)` by (L0b), with `k = 4` and `k = 3`. Then
  `(A_m, B_m)` is an exact representation of `G0`, since `G0` is a free product and so has no further
  relations. By (L0b), `lim_F ||A_m - a_m|| = lim_F ||B_m - b_m|| = 0`, and by (L0a),
  `lim_F D(A_m, B_m) = 0`.
- **Nontriviality.** `alpha, beta` generate `T` (verified by `find_words.py`), so `theta(alpha) != 1` or
  `theta(beta) != 1`. Say `theta(alpha) != 1`. Then there is `c > 0` such that the set
  `{m : ||a_m - 1|| >= c}` is `F`-stationary. On its intersection with the set where
  `||A_m - a_m|| < c`, we have `A_m != 1`.
- **Conclusion.** So for every `epsilon > 0` some nontrivial `(A_m, B_m)` has `D < epsilon`, and by
  monotonicity `delta_n -> 0`.

**Contrapositive (the sufficiency half of (3)).** If the gap holds, every homomorphism `T -> U_F` is
trivial. This uses only the verified relators and generation. It does not use completeness of the
presentation or simplicity of `T`.

## L3. `delta_n -> 0` gives an MF embedding of `T`

Pick nontrivial pairs `(A_j, B_j)` with `D(A_j, B_j) <= 1/j`. Pass to a subsequence along which, say,
`A_j != 1` for all `j` (one of the two generators is nontrivial infinitely often).
- **A homomorphism of `G0`.** `Theta(g) = [rho_j(g)]` is a homomorphism `G0 -> U_F`, since each pair is
  exact.
- **It factors through `T`.** It kills `r_1, r_2, r_P`, so it factors through
  `G0 / <<r_1, r_2, r_P>>`, which is `T` by the imported completeness of the Lochak--Schneps presentation.
- **It is nontrivial.** `||A_j - 1|| >= sqrt 2` for all `j` by (L0c), so `Theta(alpha) != 1`.
- **It is injective.** Its kernel is a proper normal subgroup of the simple group `T`, hence trivial. So
  `T` is MF.

**Negation, with (2).** `T` is not MF iff `inf { D(sigma) : sigma nontrivial irreducible } > 0` iff some
`epsilon_0 > 0` makes every `epsilon_0`-pair trivial. This is (3).

## What was checked and what was not

- **Imported.** Completeness of the Lochak--Schneps relator list (Funar--Kapoudjian, citing
  Lochak--Schneps) is used in L1 (positivity) and L3. Simplicity of `T` (CFP Thm 5.8) and Malcev's
  theorem are used there too.
- **Verified exactly.** L2 uses only the relators holding in `T` and generation, both verified in exact
  rational arithmetic.
- **Reading convention.** The criterion does not depend on the convention. `(A,B) -> (A^T, B^T)` maps
  pairs to pairs and reverses words, and `verify_ls.py` shows that the relators hold in `T` under both
  readings.
- **Not Lean-verified.**
