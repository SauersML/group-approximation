---
rg: 2
id: thompson-t-pentagon-winding-rigidity-equals-full-radical-proof
kind: route
title: Tensor the twisted defect into a subgroup of the circle, cut exact eigencorners of the finite-order rotation out of any corona model of T through the dilation maps, and cancel the scalar twist in the commutator relators
target: thompson-t-pentagon-winding-rigidity-equals-full-radical
requires:
  - thompson-t-pentagon-winding-sandwich
  - lifted-thompson-t-quotients-are-rotation-centralizers
  - thompson-t-lochak-schneps-presentation
  - central-eigencorners-die-over-full-radical-quotients
  - thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
artifacts:
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/euler_pairing.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/verify_ls.py
---

The items are numbered as in the claim. `Q` is a norm matrix corona `prod_n M_(k_n) / (+)_n M_(k_n)`.
"MF" means that there is an injective homomorphism into `U(Q)` for some `Q`. `T` is simple
(Cannon--Floyd--Parry, Thm 5.8), so `T` is MF if and only if it has a nontrivial corona representation.

## Standard corona facts

- **(C1) Lifting.** A projection `P` in `Q` lifts to projections `p_n` in `M_(k_n)`. A unitary in
  `PQP` lifts to unitaries of `p_n M_(k_n) p_n`, for `n` large. `P != 0` means that `p_n != 0` for
  infinitely many `n`.
- **(C2) Corners.** For such `P`, the corner `PQP` is `prod p_n M p_n / (+) p_n M p_n`. This is again a
  corona, of the matrix sizes `rank p_n`, after deleting the indices with `p_n = 0`.
- **(C3) Word estimates.** For unitaries, `||w(U,V) - w(U',V')||` is at most the sum over the letters of
  `w` of `||U - U'||` or `||V - V'||`. Also `||XY - 1|| <= ||X - 1|| + ||Y - 1||`.
- **(C4) Spectral rounding** (L0b of the criterion's proof). If `||u^k - 1|| < 2`, then `f(u)` is a unitary
  with `f(u)^k = 1` and `||f(u) - u|| <= (pi / 2k) ||u^k - 1||`. Here `f` moves each eigenvalue to the
  nearest `k`-th root of unity along the arc.

## (1) Lambda is a closed subgroup

- **Contains 1.** In dimension 1, `U = V = 1` gives `D_1 = 0`.
- **Products.** Take `(U,V)` in `U(n)` and `(U',V')` in `U(m)`, and put `U'' = U ⊗ U'` and
  `V'' = V ⊗ V'`. Then:
  - `||U''^4 - lambda mu|| <= ||(U^4 - lambda) ⊗ U'^4|| + ||lambda ⊗ (U'^4 - mu)|| <= D_lambda + D_mu`,
    and similarly for `V''^3` and for `(V''U'')^5` against `(lambda mu)^3`;
  - `r_i(U'',V'') = r_i(U,V) ⊗ r_i(U',V')`, so by (C3) it lies within `D_lambda + D_mu` of 1.

  Hence `D_(lambda mu)(U'',V'') <= D_lambda(U,V) + D_mu(U',V')`, and `Lambda Lambda ⊆ Lambda`.
- **Inverses.** Entrywise conjugation gives `D_(conj lambda)(conj U, conj V) = D_lambda(U,V)`.
- **Closed.** `|lambda^3 - lambda'^3| <= 3 |lambda - lambda'|` gives
  `D_lambda <= D_lambda' + 3 |lambda - lambda'|`.

## (0) Relations of T-bar, and a finite presentation of it

- **Reading convention.** Fix the reading convention of `euler_pairing.py`. Under the other convention,
  every word is replaced by its reverse. Inversion `g -> g^(-1)` identifies `T̄` with its opposite group,
  so every step below goes through verbatim.
- **Relations.** That script evaluates `a^4`, `b^3`, `(ba)^5`, `r_1` and `r_2` exactly on
  `(alpha-bar, beta-bar)`, as the integer translations `1, 1, 3, 0, 0`. So in `T̄`:

  ```text
  alpha-bar^4 = beta-bar^3 = z,   (beta-bar alpha-bar)^5 = z^3,   r_1 = r_2 = 1.     (R)
  ```

- **Presentation.** Let

  ```text
  E = < a, b | [a^4, b], a^4 b^(-3), (ba)^5 a^(-12), r_1, r_2 >,   c = a^4.
  ```

  - `c` commutes with `b` by the first relator, and with `a` trivially, so `c` is central in `E`.
  - By (R) there is a homomorphism `phi : E -> T̄` with `a -> alpha-bar`, `b -> beta-bar` and `c -> z`.
  - `phi` is onto. `alpha`, `beta` generate `T` (`thompson-t-lochak-schneps-presentation`), so the image
    maps onto `T`, and it contains `z = alpha-bar^4`, which generates `ker(T̄ -> T)`.
  - `E/<c>` is `<a, b | a^4, b^3, (ba)^5, r_1, r_2>`. By completeness of the Lochak--Schneps presentation
    this is `T`, and `E -> T̄ -> T` is this quotient map. So `ker phi ⊆ <c>`.
  - `phi(c^m) = z^m` is the translation by `m`, which is nontrivial for `m != 0`. So `phi` is injective,
    and `E ≅ T̄`.
- **Perfect.** `E^ab = Z^2 / < (4,-3), (-7,5) >`. The relator `(ba)^5 a^(-12)` has exponent sums
  `(5 - 12, 5) = (-7, 5)`. The determinant is `20 - 21 = -1`, so `E^ab = 0` and `T̄` is perfect.
- **Corona form.** By this presentation, a corona representation `pi` of `T̄` with `pi(z) = lambda 1` is
  the same as a pair of unitaries `u, v` in `Q` with

  ```text
  u^4 = v^3 = lambda,   (vu)^5 = lambda^3,   r_1(u,v) = r_2(u,v) = 1.
  ```

  The relator `[a^4, b]` holds automatically, because `lambda` is a scalar. By (C1) this is the same as a
  sequence of pairs `(U_n, V_n)` in `U(k_n)` with `D_lambda(U_n, V_n) -> 0`.
- **Corollary.** `lambda` lies in `Lambda` if and only if `T̄` has a corona representation with
  `z -> lambda 1`.
  - If `inf D_lambda = 0`, pick pairs with `D_lambda -> 0`. Then `(U_n, V_n)` defines such a `pi` in the
    corona of the sizes `n_m`.
  - Conversely, lift a given `pi`.

## (2) T MF puts every 2-power root of unity in Lambda

Let `rho : T -> U(Q)` be a nontrivial corona representation. Fix `k >= 1`, write `t_k` for the rotation by
`2^(-k)`, and put `zeta = e^(2 pi i/2^k)`.

- **The dilation map.** By `lifted-thompson-t-quotients-are-rotation-centralizers`,
  `iota_k(g) = p(2^(-k) g(2^k .))` is a homomorphism `T̄ -> T` with image `C_T(t_k)` and
  `iota_k(z) = t_k`. Put `pi = rho o iota_k : T̄ -> U(Q)`, and `R = pi(z) = rho(t_k)`.
- **Exact eigenprojections.** `t_k` has order `2^k`, so `R^(2^k) = 1` **exactly** in `Q`. For
  `j in Z/2^k`, put

  ```text
  P_j = 2^(-k) sum_{m=0}^{2^k - 1} zeta^(-jm) R^m.
  ```

  These are projections in `Q` with `sum_j P_j = 1` and `R P_j = zeta^j P_j`. Each `P_j` lies in the
  C*-algebra generated by `R`. `pi(T̄)` lies in `rho(C_T(t_k))`, which commutes with `R`, so each `P_j`
  lies in `pi(T̄)' ∩ Q`.
- **An odd eigenvalue occurs.** `R^(2^(k-1)) = rho(t_k^(2^(k-1))) = rho(J)`, where `J = alpha^2` is the
  half-turn. So

  ```text
  sum_{j odd} P_j = (1 - rho(J)) / 2.
  ```

  If this is 0, then `J` lies in `ker rho`. `J != 1` and `T` is simple, so `rho` is trivial, which is a
  contradiction. Hence `P_j != 0` for some odd `j`.
- **Compress.** `P_j` commutes with `pi(T̄)`, so `g -> P_j pi(g) P_j` is a unitary representation of `T̄`
  in the corner `P_j Q P_j`, with `z -> zeta^j P_j`. By (C2) that corner is a norm matrix corona. By the
  corollary of (0), `zeta^j` lies in `Lambda`.
- **Generate.** Since `j` is odd, it is invertible mod `2^k`: `j j' ≡ 1`. By (1),
  `zeta = (zeta^j)^(j')` lies in `Lambda`.
- **Conclude.** `Lambda` contains `e^(2 pi i/2^k)` for all `k`. It is a subgroup, so it contains all dyadic
  roots of unity, which are dense. It is closed, so `Lambda = S^1`.

No approximation estimate enters (2). The eigenprojections are exact, because `rho(t_k)` has exact finite
order in `Q`. This is the point where the finite central quotients `T̄/<z^(2^k)> ≅ C_T(t_k)` do the work.
The dead torus-knot lane needed eigencorners of an infinite-order `rho(z)`, and no mechanism for forcing those is known.

## (3) A small twist rescales to an exact pair with nonzero winding

Let `lambda = e^(i theta)` lie in `Lambda`, with `0 < |theta| <= pi`, and let `eta > 0`. Pick unitaries
`U, V` in some `U(n)` with `D_lambda(U,V) < eta`.

- **Untwist.** Put `U' = e^(-i theta/4) U` and `V' = e^(-i theta/3) V`. Then `||U'^4 - 1|| < eta` and
  `||V'^3 - 1|| < eta`. By (C4) there are exact `A = f(U')` and `B = f(V')` with `A^4 = B^3 = 1`, and
  - `||A - U'|| <= (pi/8) eta`;
  - `||B - V'|| <= (pi/6) eta`.
- **The commutator relators do not see the twist.** Scaling `(U,V)` by scalars multiplies `X = BAB` by a
  scalar `s`. The conjugates `JXJ^(-1)` and `WXW^(-1)` are multiplied by the same `s`. The scalars cancel
  in a commutator, so `r_i(U',V') = r_i(U,V)` exactly.
- **Letter counts.** `r_1` has 12 letters `a^(±1)` and 8 letters `b^(±1)`. `r_2` has 20 and 16.
- **Relator bounds.** By (C3):
  - `||r_1(A,B) - 1|| <= eta + (12 pi/8 + 8 pi/6) eta < 10 eta`;
  - `||r_2(A,B) - 1|| <= eta + (20 pi/8 + 16 pi/6) eta < 18 eta`.
- **The pentagon sees the twist with weight -1.** Compute

  ```text
  (V'U')^5 = e^(-5 i theta (1/4 + 1/3)) (VU)^5 = e^(-35 i theta/12) (VU)^5 ,
  ```

  and `(VU)^5` is within `eta` of `lambda^3 = e^(36 i theta/12)`. So `(V'U')^5` is within `eta` of
  `e^(i theta/12)`. Then (C3), with 5 letters of each kind, gives

  ```text
  || (BA)^5 - e^(i theta/12) || <= eta + 5 (pi/8 + pi/6) eta < 6 eta .
  ```

- **The defect.** Hence `D(A,B) <= max(18 eta, |e^(i theta/12) - 1| + 6 eta) < |theta|/12 + 20 eta`.
- **The winding.** Suppose `6 eta < 2 sin(|theta|/24)`. Every eigenvalue of `M = (BA)^5` is within chordal
  distance `2 sin(|theta|/24)` of `e^(i theta/12)`, that is, within angle `|theta|/12` of it. So for
  `theta > 0` every eigenvalue angle lies in `(0, theta/6)`, and for `theta < 0` in `(theta/6, 0)`. These
  intervals are inside `(-pi, pi)`, so the principal logarithm applies, and

  ```text
  kappa_P = (1/2 pi) sum_j phi_j
  ```

  has the sign of `theta` and is nonzero, because `n >= 1`. By item (1) of the sandwich,
  `kappa_P ∈ (1/12) Z`, so `|kappa_P| >= 1/12`. With every `|phi_j| < |theta|/6`, this forces
  `n > pi/|theta|`. This is consistent with the fact that each fixed dimension is gapped.

## (4) The equivalence

- **(PW) implies T not MF.** Suppose that `T` is MF, and let `delta > 0`. By (2), `Lambda = S^1`.
  - Choose `theta` with `0 < theta < 6 delta`, which makes `theta/12 < delta/2`.
  - Choose `eta` with `20 eta < delta/2` and `6 eta < 2 sin(theta/24)`.

  Then (3) gives an exact pair with `D(A,B) < delta` and `kappa_P != 0`. So (PW) fails for every `delta`.
- **T not MF implies (PW).** This is the first arrow of `thompson-t-pentagon-winding-sandwich`. It goes
  through `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`: every `epsilon_0`-pair is `(1,1)`, and so
  has `kappa_P = 0`.
- **T not MF implies Lambda = {1}.** Let `lambda` lie in `Lambda`. By the corollary of (0), there is a
  corona representation `pi : T̄ -> U(Q)` with `pi(z) = lambda 1`. Apply item 1 of
  `central-eigencorners-die-over-full-radical-quotients` with:
  - `G = T̄`, which is perfect by (0);
  - `c = z`, which is central;
  - `G/<c> = T`, which has full radical because `T` is not MF;
  - `P = 1`, which lies in `pi(G)' ∩ Q`, and `pi(c) P = lambda P`.

  Item 1 gives `pi(g) = 1` for every `g`. In particular `lambda 1 = pi(z) = 1`, and `Q != 0`, so
  `lambda = 1`.
- **Closing the cycle.**
  - `Lambda = {1}` implies `lambda_0 ∉ Lambda` for every `lambda_0 != 1`.
  - `lambda_0 ∉ Lambda` for one `lambda_0` implies `Lambda != S^1`.
  - `Lambda != S^1` implies `T` is not MF, by (2).

  So all five conditions are equivalent, and `Lambda` is `{1}` if `T` is not MF and `S^1` if `T` is MF.

## (5) The one-point form

Take `lambda_0 = -1`. By (4), `T` is MF if and only if `-1 ∈ Lambda`.

- **Substituting `V -> -V`.** This maps `D_(-1)`-small pairs bijectively to pairs with:
  - `U^4 ≈ -1`, `V^3 ≈ 1` and `(VU)^5 ≈ 1`, because `(-V)^3 = -V^3` and `(-VU)^5 = -(VU)^5`;
  - `r_i` unchanged, because of the scalar cancellation in (3).
- **The centralizer form.** By the corollary of (0), `-1 ∈ Lambda` if and only if `T̄` has a corona
  representation with `z -> -1`.
  - Such a representation kills `z^2`, so it factors through `T̄/<z^2>`. By
    `lifted-thompson-t-quotients-are-rotation-centralizers` (`k = 1`), `iota_1` identifies `T̄/<z^2>` with
    `C_T(J)` and sends `z` to `J`. So it is a corona representation of `C_T(J)` with `J -> -1`.
  - Conversely, composing such a representation of `C_T(J)` with `iota_1` gives a representation of `T̄`
    with `z -> -1`.

## Dependencies and what was not checked

- **Used.**
  - Completeness of the Lochak--Schneps presentation, in (0) and in the sandwich's first arrow.
  - The exact Euler numbers of `euler_pairing.py`, which give (R).
  - Simplicity of `T` (Cannon--Floyd--Parry).
  - The dilation isomorphisms `T̄/<z^(2^k)> ≅ C_T(t_k)`.
  - Item 1 of the eigencorner lemma. This is used only for "T not MF implies `Lambda = {1}`". The
    equivalence of (PW) with "T not MF" does not use it.
- **No Kazhdan input.** No property (T) is used anywhere, and no approximation estimate is used in (2).
- **Not Lean-verified.**
