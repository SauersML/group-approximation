---
rg: 2
id: thompson-v-mf-iff-opnorm-s4-s3-defect-gap-proof
kind: route
title: Correct both finite subgroups in operator norm, align the two copies of a by a near-identity unitary, and read off irreducible summands
target: thompson-v-mf-iff-opnorm-s4-s3-defect-gap-vanishes
requires:
  - thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3
  - thompson-v-finitely-presented-infinite-simple
  - thompson-v-has-no-nontrivial-fd-unitary-representation
  - finite-group-opnorm-support-profile
  - countable-group-mf-conventions
artifacts:
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/delta_n.py
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/scan_n2.py
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/calibrate_ctrl2.py
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/out_scan_n2_V.json
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/out_V.json
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/log_V.txt
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/log_CTRL2.txt
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/out_CTRL2.json
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/out_calibrate_ctrl2_opnorm.json
  - experiments/thompson-v-opnorm-defect-gap-2026-09-17/out_calibrate_ctrl2_hswarm.json
---

Numbering follows the claim. `||.||` is the operator norm. Throughout, `pi : G0 -> V` is the quotient map of
`thompson-v-is-a-four-relator-quotient-of-s4-amalgam-s3`, with kernel `<<r5, ..., r8>>`; `S4 = <a,b>` and
`S3 = <a,c>` embed in `G0`, and (through `pi`) in `V`.

**MF convention.** For a filter `F` on `N` (the Frechet filter or a free ultrafilter) and dimensions
`d_m >= 1`, put `U_F = prod_m U(d_m) / N_F`, where `N_F = {(u_m) : lim_F ||u_m - 1|| = 0}`. `V` is MF iff it
has an injective homomorphism into some `U_F`. For the Frechet filter this is the unitary-sequence
definition, and `countable-group-mf-conventions` identifies it with the C*-corona definition. The
argument below produces and consumes both filter versions, so it does not depend on the choice.

## L0. Two elementary facts

**(L0a) Words are Lipschitz.** If `x_j, y_j` are unitaries with `||x_j - y_j|| <= eta`, then a word `w` of
length `l` satisfies `||w(x) - w(y)|| <= l eta`. This is telescoping, since unitaries and their inverses have
norm 1.

**(L0b) Aligning two involutions.** Let `S, T` be self-adjoint unitaries in `M_d` with `||S - T|| < 2`. Then
there is a unitary `Z` with `Z T Z^* = S` and `||Z - 1|| <= ||S - T||`.

*Proof.* Put `P = (1 - S)/2` and `Q = (1 - T)/2`, so `eta = ||P - Q|| = ||S - T||/2 < 1`. Let
`X = PQ + (1 - P)(1 - Q)`.
- **X is close to 1.** Expanding, `X - 1 = 2PQ - P - Q = (P - Q)(2Q - 1)`. Since `2Q - 1` is unitary,
  `||X - 1|| <= eta < 1`, so `X` is invertible and its singular values lie in `[1 - eta, 1 + eta]`.
- **X intertwines Q and P.** `XQ = PQ = PX`.
- **|X| commutes with Q.** `X^* X Q = X^* P X = (PX)^* X = (XQ)^* X = Q X^* X`, using `P^* = P`.
- **The polar part.** Hence `Z = X |X|^(-1)` is unitary and `Z Q = X Q |X|^(-1) = P X |X|^(-1) = P Z`.
  So `Z Q Z^* = P`, hence `Z T Z^* = S`. Finally
  `||Z - 1|| <= ||X|X|^(-1) - X|| + ||X - 1|| = || 1 - |X| || + ||X - 1|| <= 2 eta = ||S - T||`.

## L1. Structure of `delta_n`

**(L1a) The trivial representation, and 1-dimensional representations.** `a` is a transposition in both
`S4` and `S3`, and in each of them the normal closure of a transposition is the whole group. Hence
`rho(a) = 1` forces `rho` to be trivial on `S4` and on `S3`, which generate `G0`. So `rho(a) != 1` iff
`rho` is nontrivial. This is the second sentence of (2).

A homomorphism `G0 -> U(1)` has `b^3 = 1` and `(ab)^4 = a^4 b^4 = b = 1`, and `(ac)^3 = a^3 c^3 = ac = 1`, so
`c = a`. The only nontrivial one is therefore `eta : a, c -> -1`, `b -> 1`. It sends `r_i` to
`(-1)^(e_i)`, where `e_i` is the total exponent of `a` and `c` in `r_i`. If every `e_i` were even, `eta` would
factor through `V`, contradicting `thompson-v-has-no-nontrivial-fd-unitary-representation`. So some
`eta(r_i) = -1`, and `delta_1 = D(eta) = 2`.

**(L1b) Direct sums.** The words are evaluated blockwise, so `D(rho_1 (+) rho_2) = max(D(rho_1), D(rho_2))`,
and `D(1) = 0`.
- If `rho(a) != 1` then `(rho (+) 1)(a) != 1`. Hence `delta_(n+1) <= delta_n`.
- **(2), irreducible form.** Finite-dimensional unitary representations are completely reducible.
  - If `rho(a) != 1`, then `rho` is nontrivial by (L1a). So it has a nontrivial irreducible summand
    `sigma`, with `dim sigma <= n` and `D(sigma) <= D(rho)`.
  - Conversely, a nontrivial irreducible `sigma` with `dim sigma <= n` gives
    `rho = sigma (+) 1_(n - dim sigma)`, with `rho(a) != 1` and `D(rho) = D(sigma)`.
  - So the two infima agree. The minimum over irreducibles is attained once `delta_n` is, by the first
    bullet applied to a minimiser.

**(L1c) Normal form and compactness: (4) and (1).**
- **Normal form.** Let `rho(a)` have `-1`-eigenspace of dimension `k`.
  - Decompose `rho|_S4` into irreducibles. By a unitary change of basis, `rho|_S4` becomes a fixed block sum
    `rho_4`, arranged so that `rho_4(a) = diag(1_(n-k), -1_k)`. Only finitely many multiplicity vectors
    occur in dimension `n`.
  - In that basis `rho|_S3` is unitarily equivalent to the fixed block sum `rho_3` with the same
    multiplicities, again arranged so that `rho_3(a) = diag(1_(n-k), -1_k)`. Write `rho|_S3 = Y rho_3 Y^*`.
  - Then `Y` commutes with `diag(1_(n-k), -1_k)`, so `Y` lies in `U(n-k) x U(k)`.
  - Conversely, every such pair `(rho_4, Y rho_3 Y^*)` agrees on `a` and defines a representation of the
    amalgam `G0`.
- **Compactness.** So the set of `rho` with `rho(a) != 1`, up to conjugacy, is a finite union of continuous
  images of the compact groups `U(n-k) x U(k)` with `k >= 1`. `D` is continuous and conjugation-invariant, so
  `delta_n` is attained.
- **Positivity.** If `delta_n = 0`, a minimiser `rho` kills `r5, ..., r8`, hence factors through `V`. It is
  nontrivial by (L1a). This contradicts `thompson-v-has-no-nontrivial-fd-unitary-representation`. So
  `delta_n > 0`, which completes (1).

**(L1d) Arithmetic form: (5).** "There is `rho : G0 -> U(n)` with `rho(a) != 1` and `D(rho) < q`" is a
first-order sentence over the real field with rational coefficients:
- the variables are the real and imaginary parts of three `n x n` matrices `A, B, C`;
- the constraints are unitarity, the five defining relations of `G0`, `A != 1`, and, for each `i`,
  positive definiteness of `q^2 - (r_i(A,B,C) - 1)^*(r_i(A,B,C) - 1)`.

Tarski--Seidenberg decides it. Together with (3) and `delta_(n+1) <= delta_n`, "V is MF" is
`forall k exists n : delta_n < 1/k`.

## L2. MF gives small-defect exact representations: (3), forward direction

Let `theta : V -> U_F` be an injective homomorphism. Choose unitary lifts `(x_m)` of `theta(pi(x))` for
`x in {a, b, c}`. Nothing below requires `x_m` to satisfy any relation exactly.

**(i) Every word trivial in V has a vanishing lift.** If `pi(w) = 1`, then `[w(x_m)] = theta(pi(w)) = 1`,
i.e. `lim_F ||w(x_m) - 1|| = 0`.

**(ii) Correcting each finite subgroup.** For `h` in `S4` fix a word `u_h` in `a, b`, with `u_a = a` and
`u_e` empty, and put `phi_m(h) = u_h(x_m)`.
- For each of the finitely many pairs `(g, h)`, the word `u_(gh)^(-1) u_g u_h` is trivial in `S4`, hence in
  `V`. By (i), the all-pairs defect `eps_m = max_(g,h) ||phi_m(g) phi_m(h) - phi_m(gh)||` has
  `lim_F eps_m = 0`.
- By `finite-group-opnorm-support-profile` there are constants `eps_4 > 0` and `C_4`, depending only on
  `S4` and the chosen words, such that whenever `eps_m <= eps_4` there is an exact representation
  `rho_4,m : S4 -> U(d_m)` with `||rho_4,m(h) - phi_m(h)|| <= C_4 eps_m` for all `h`. That node states the
  correction for a fixed presentation model; its proof starts from exactly this all-pairs map.
- The same holds for `S3`, with words in `a, c` and `u_a = a`: exact `rho_3,m`, with constants `eps_3, C_3`.

Put `C_0 = max(C_4, C_3)`. On the `F`-large set where `eps_m <= min(eps_4, eps_3)`:
`||rho_4,m(a) - a_m|| <= C_0 eps_m` and `||rho_3,m(a) - a_m|| <= C_0 eps_m`.

**(iii) Gluing.** Now restrict further to where `2 C_0 eps_m < 2`.
- `S = rho_4,m(a)` and `T = rho_3,m(a)` are self-adjoint unitaries with `||S - T|| <= 2 C_0 eps_m < 2`.
- (L0b) gives a unitary `Z_m` with `Z_m T Z_m^* = S` and `||Z_m - 1|| <= 2 C_0 eps_m`.
- Then `rho_4,m` and `Z_m rho_3,m Z_m^*` agree on `<a>`. By the universal property of the amalgam, they
  define a homomorphism `rho_m : G0 -> U(d_m)`.
- Its generators satisfy `||rho_m(x) - x_m|| <= 5 C_0 eps_m` for `x = a, b, c`. For `c`:
  `||Z rho_3(c) Z^* - c_m|| <= 2 ||Z - 1|| + ||rho_3(c) - c_m||`.

**(iv) Defect and nontriviality.**
- **Defect.** By (L0a) and (i), `||rho_m(r_i) - 1|| <= |r_i| . 5 C_0 eps_m + ||r_i(x_m) - 1||`, which
  tends to 0 along `F`. So `lim_F D(rho_m) = 0`.
- **Nontriviality.** `pi(a) != 1` (`S4` embeds in `V`) and `theta` is injective, so `theta(pi(a)) != 1`.
  That is, `A_c = {m : ||a_m - 1|| >= c}` is `F`-stationary (meets every set of `F`) for some `c > 0`. On
  `A_c` intersected with the sets above, `||rho_m(a) - 1|| >= c - 5 C_0 eps_m > 0` eventually. So
  `rho_m(a) != 1` there.
- **Conclusion.** Hence for every `epsilon > 0` some `m` has `rho_m(a) != 1` and `D(rho_m) < epsilon`. So
  `delta_(d_m) < epsilon`. By `delta_(n+1) <= delta_n`, `delta_n < epsilon` for all `n >= d_m`. So
  `delta_n -> 0`.

## L3. Small-defect exact representations give MF: (3), converse direction

Suppose `delta_n -> 0`. Pick `rho_j : G0 -> U(n_j)` with `rho_j(a) != 1` and `D(rho_j) <= 1/j`.
- **A homomorphism into the corona.** Let `F` be the Frechet filter, or any free ultrafilter, on the
  index `j`. Then `Theta(g) = [rho_j(g)]` is a homomorphism `G0 -> U_F`, because each `rho_j` is exact.
- **It factors through V.** `||rho_j(r_i) - 1|| <= 1/j -> 0`, so `Theta(r_i) = 1` for `i = 5..8`. Hence
  `Theta` factors through `pi` as `theta : V -> U_F`.
- **It is nontrivial.** `rho_j(a)` is an exact involution different from 1, so it has eigenvalue `-1`,
  and `||rho_j(a) - 1|| = 2` for every `j`. Hence `theta(pi(a)) != 1`, and no filter or ultrafilter can
  change that. No amplification is needed, unlike `classical-unitary-ratio-witnesses-amplify-to-metric-models`.
- **It is injective.** `ker theta` is a normal subgroup of the simple group `V`
  (`thompson-v-finitely-presented-infinite-simple`), and it does not contain `pi(a)`. So it is trivial,
  and `V` is MF under both filter conventions.

**Negation.** With (2) and the monotonicity in (L1b), `delta_n -> 0` iff
`inf { D(sigma) : sigma nontrivial irreducible } = 0`. Negating gives the displayed form of (3).

## What was checked and what was not

- **Written proof.** Every step above is elementary, apart from the two imported statements: same-dimension
  operator-norm correction for finite groups, and the MF convention equivalence.
- **Not Lean-verified.**
- **The words.** The computation in `delta_n.py` evaluates `r5, ..., r8` as matrix products, letter by
  letter, from `experiments/thompson-v-models/rel_V.txt`. The criterion does not depend on the reading
  convention: `rho -> rho^T` is a bijection between representations of `G0`, because each defining
  relator of `G0` is conjugate to its own reversal. It turns the defect of a word into the defect of the
  reversed word.

## Computation (not part of the proof)

All files are in `experiments/thompson-v-opnorm-defect-gap-2026-09-17/`.

- **`delta_2`, certified up to floating point.** `scan_n2.py` scans the one free angle of the normal form (4)
  in dimension 2 (`W = diag(1, e^(i theta))`) on `4 * 10^5` points. It uses the Lipschitz bound
  `|dD/dtheta| <= max_i #c(r_i) = 14`, which holds because `||[E, C]|| <= 1` for a projection `E`. Output
  `out_scan_n2_V.json`:
  - `1.92374 <= delta_2 <= 1.92385`, attained by gluing the 2-dimensional irreducibles of `S4` and `S3`;
  - every other `n = 2` pattern has `D = 2` identically.
- **Local search, `n <= 7`.** `delta_n.py --restarts 6 --iters 250` covers every multiplicity pattern that
  is not pruned. It prunes patterns that contain a 1-dimensional summand because the `S4`- and
  `S3`-isotypic parts of one character have total dimension `> n`. Output `out_V.json`, `log_V.txt`.

  | n | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
  |---|---|---|---|---|---|---|---|
  | V, best D at this n | 2 | 1.9239 | 1.7441 | 1.6876 | 1.6798 | 1.6975 | 1.7022 |
  | PSL(2,17) control, best D at this n | 2 | 1.8434 | 1.6894 | 1.7051 | 1.6030 | 1.6472 | 1.6464 |

  So the running upper bound is `delta_7 <= 1.6798` for V. The control continues to `n = 8`: `1.6562` and
  `n = 9`: `1.7044` (`out_CTRL2.json`). **The control's own exact 9-dimensional solutions (the two
  9-dimensional irreducibles of PSL(2,17)) are missed at n = 9.**
- **Calibration fails.** `calibrate_ctrl2.py` builds the 17-dimensional Steinberg representation `St` of
  the planted control `PSL(2,17)`. It checks `D(St) = 5e-15` and computes its multiplicity pattern:
  - `S4`: `1 + 2*[2] + 2*[3] + 2*[3s]`;
  - `S3`: `3*[1] + 2*[sgn] + 6*[2]`;
  - `k = 8`.

  It then runs the same local search on that one pattern:

  | search | best D | output |
  |---|---|---|
  | op-norm loss, 8 restarts, 600 iterations | 1.7645 | `out_calibrate_ctrl2_opnorm.json` |
  | 1000 iterations of smooth Frobenius loss, then op-norm loss, 1500 iterations in all | 1.7658 | `out_calibrate_ctrl2_hswarm.json` |

  In both runs the exact solution `D = 0` lies inside the searched set.
- **Reading.** For these word lengths (26 to 37), the local-search landscape in the normal form has
  plateaus around `D ~ 1.6-1.77`. These plateaus are the same for V and for a planted control that has
  exact solutions. The numbers above are therefore valid upper bounds on `delta_n`. They are **no
  evidence** for or against the uniform gap in (3), beyond the certified value of `delta_2`.
- **Permutation models.** For every nontrivial permutation representation of `G0`, `D >= sqrt 3`
  (see `thompson-v-is-not-mf`, Attempts). The minimisers found for `n >= 3` have `D < sqrt 3`, so they
  are not permutation models.
