---
rg: 2
id: thompson-t-mf-iff-finite-quotient-corners-proof
kind: route
title: Pad an exact pair by Willett's R_q-stability of K(3,4), retwist the central element to land in a finite quotient of Z/4 * Z/3, and cut the original block back out as an almost-invariant corner; conversely polar-round a corner; average a corner over F to get the diameter bound
target: thompson-t-mf-iff-finite-quotient-corners
requires:
  - thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes
  - torus-knot-groups-are-rq-stable
  - lie-closure-trichotomy-without-finite-quotients
  - thompson-t-lochak-schneps-presentation
---

The notation is that of the target. `||.||` is the operator norm. Words are over the letters
`a^(+-1), b^(+-1)`. As such words, `r_1 = [bab, a^2 bab a^2]` has length 20,
`r_2 = [bab, a^2 b^2 a^2 bab a^2 b a^2]` has length 34, and `r_P = (ba)^5` has length 10. Put `L = 34`.
The lemmas (L0a) (words are Lipschitz), (L0b) (spectral rounding, `||f(u) - u|| <= (pi/2k)||u^k - 1||`)
and (L0c) (a nontrivial exact pair has `||A - 1|| >= sqrt 2` or `||B - 1|| >= sqrt 3`) are those of
`thompson-t-mf-iff-opnorm-z4-z3-defect-gap-proof`.

## Step 0. Corner calculus

Let `P` be a projection and `V_1, ..., V_m` operators of norm `<= 1` with `||[P, V_j]|| < eps`. Since
`(1-P)[P,V]P = -(1-P)VP` and `P[P,V](1-P) = PV(1-P)`, both off-diagonal blocks of each `V_j` have norm
`< eps`.

**(K1) Compression of products.** `||P V_1 ... V_m P - (P V_1 P)(P V_2 P) ... (P V_m P)|| <= (m-1) eps`.

*Proof.* `P V_1 W P - (P V_1 P)(P W P) = P V_1 (1-P) W P`, whose norm is at most `||P V_1 (1-P)|| < eps`.
Apply this with `W = V_2 ... V_m` and induct, noting that `P V_1 P` is a contraction.

For unitary `V`, `[P, V^*] = -[P, V]^*`, so the hypothesis for a letter gives it for its inverse.

## Step 1. (2 => 1): a corner gives a nontrivial exact pair

Let `(F, pi, P)` be an `eps`-corner with `eps < 1/4`. Let `n = rank P` and identify `ran P` with `C^n`.
For `s in {a, b}` put `X_s = P pi(s) P`, an operator on `C^n`.

1. **Near-unitarity.** `X_s^* X_s = P - P pi(s)^* (1-P) pi(s) P`, so `||X_s^* X_s - 1|| < eps^2`. Hence
   `X_s` is invertible and `|| |X_s| - 1 || < eps^2`, using `|t - 1| <= |t^2 - 1|` for `t >= 0`. Let
   `U_s = X_s |X_s|^(-1)`, a unitary. Then `||X_s - U_s|| = ||U_s(|X_s| - 1)|| < eps^2`. Also
   `P pi(s)^(-1) P = X_s^*`, which is within `eps^2` of `U_s^*`.
2. **Words.** For a word `w` of length `m`, (K1) and step 1 give
   `||P pi(w) P - w(U_a, U_b)|| <= (m-1) eps + m eps^2 <= 2 m eps`.
3. **Exact rounding.** `pi(a)^4 = 1` and `pi(b)^3 = 1` in `F`. So by step 2, `||U_a^4 - 1|| <= 8 eps` and
   `||U_b^3 - 1|| <= 6 eps`. By (L0b) there are unitaries `A, B` with `A^4 = B^3 = 1`,
   `||A - U_a|| <= (pi/8) 8 eps = pi eps` and `||B - U_b|| <= (pi/6) 6 eps = pi eps`.
4. **Defect.** For `r` in `{r_1, r_2, r_P}` of length `l <= 34`, (L0a), step 2 and (C2) give
   `||r(A,B) - 1|| <= ||r(U) - 1|| + 34 pi eps <= ||P(pi(r) - 1)P|| + 68 eps + 34 pi eps < 176 eps`.
5. **Nontriviality.** By (C3), say `||X_a - 1|| >= 1`. Then
   `||A - 1|| >= 1 - eps^2 - pi eps > 1 - 1/16 - pi/4 > 0`, so `A != 1`. The case of `b` is the same.

So `(A, B)` is a nontrivial exact pair in `U(n)` with `D(A, B) < 180 eps`. If (2) holds, such pairs
exist for every `eps > 0`. By item 3 of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`, `T` is then
MF. This proves (2 => 1) and the second quantitative form. (3 => 2) is trivial.

## Step 2. (1 => 3): an exact pair gives a corner in a finite group

**The input, verbatim.** Willett, arXiv:2408.13350, Definition 1.6, as quoted in
`torus-knot-groups-rq-stable-citation`: "The group Γ is Q-R-stable if for any finite subset S of Γ and
ϵ > 0 there exists a finite subset T of Γ and δ > 0 such that if ϕ: Γ → M_n(C)_1 is a
(T,δ)-representation, then there exists a map θ: Γ → M_k(C) in Q(S,ϵ) and a representation
π: Γ → M_{n+k}(C) in R such that ‖(ϕ(s) ⊕ θ(s)) − π(s)‖ < ϵ for all s ∈ S." Remark 1.8 fixes
"Q = R = R_q", with R_q "the class of finite-dimensional representations that factor through a finite
quotient of Γ". `torus-knot-groups-are-rq-stable` gives this for `K = K(3,4) = <x, y | x^4 = y^3>`.

**On unitarity.** The representations in `R` are unitary. Willett's Definition 1.4 asks for "a unitary
representation π: Γ → M_n(C)". His Remark 1.7 says that "Stability of Γ is the case of Q-R-stability
where Q is the zero quasi-representation on the zero vector space, and R consists of all
finite-dimensional representations". His introduction says "We study this in the context of unitary
representations of discrete groups, and where the approximations take place in the operator norm". This
is also the reading used in `thompson-t-padded-cover-stability-is-inert`. The map `θ` is not used below.

**Construction.** Assume `T` is MF and fix `eps` with `0 < eps <= 1`.
- By item 3 of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes` there is a nontrivial exact pair
  `(A, B)` in `U(n)` with `D(A, B) < eps/2`.
- Let `c = x^4 = y^3`, which is central in `K`. Since `A^4 = 1 = B^3`, the assignment `x -> A`, `y -> B`
  defines an honest unitary representation `phi : K -> U(n)`. It is unital, takes values in
  `M_n(C)_1`, and is a `(T', delta)`-representation for every finite `T'` and every `delta > 0`.
- Apply the input with `S = {x, y, x^(-1), y^(-1), c}` and `eps' = eps/300`. This gives a unitary
  representation `pi : K -> U(n + k)` that factors through a finite quotient of `K`, and a map `theta`,
  with `||pi(s) - (phi(s) (+) theta(s))|| < eps'` for `s` in `S`.
- Let `P` be the projection onto the first summand `C^n`. Then `phi(s) (+) theta(s)` commutes with `P`,
  and its compression to `ran P` is `phi(s)`. Hence, for `s` in `S`:

  ```text
  (a)  ||(1-P) pi(s) P|| < eps',  ||P pi(s) (1-P)|| < eps',  ||P pi(s) P - phi(s)|| < eps',
  (b)  ||(pi(c) - 1) P|| < eps'       (because phi(c) = A^4 = 1).
  ```

**Central retwist.** In `pi`, the orders of `pi(x)` and `pi(y)` need not divide 4 and 3. The retwist fixes
this without moving the corner.
- `z = pi(c)` is a unitary of finite order `q`, and it commutes with `pi(K)`, since `c` is central.
- For `lambda = e^(it)` with `t` in `(-pi, pi]`, put `mu(lambda) = e^(it/4)` and `nu(lambda) = e^(it/3)`.
  Let `M = mu(z)` and `N = nu(z)` by functional calculus. They commute with `pi(K)` and with each other,
  and satisfy `M^4 = N^3 = z` and `M^(4q) = N^(3q) = 1`.
- Put `a' = pi(x) M^*` and `b' = pi(y) N^*`. Then `a'^4 = z (M^*)^4 = 1` and `b'^3 = z (N^*)^3 = 1`. So
  `a -> a'`, `b -> b'` is a unitary representation of `G0`.
- Its image `F = <a', b'>` lies in the group generated by the finite group `pi(K)` and the finite abelian
  group `<M, N>`, which centralises it. So `F` is finite, and `(F, a', b')` is a finite quotient of `G0`.
  Let `pi_F` be the identity representation of `F` on `C^(n+k)`.

**The retwist does not move the corner.** For `|t| <= pi`, `|e^(it) - 1| = 2 sin(|t|/2) >= 2|t|/pi`, so
`|mu(lambda) - 1| <= |t|/4 <= (pi/8) |lambda - 1|` and `|nu(lambda) - 1| <= (pi/6) |lambda - 1|`. The same
bounds hold for the conjugates. For a normal `z` and functions with `|f| <= C|g|` on its spectrum,
`||f(z) xi|| <= C ||g(z) xi||` for every vector `xi`. So by (b):

```text
||(M^(+-1) - 1) P|| < (pi/8) eps',        ||(N^(+-1) - 1) P|| < (pi/6) eps'.
```

Now `a' P - pi(x) P = pi(x)(M^* - 1) P`, and `a'^* P - pi(x)^* P = pi(x)^* (M - 1) P` because `M` commutes
with `pi(x)`. So `||(a'^(+-1) - pi(x^(+-1))) P|| < eps'`, and likewise for `b'`. Combining this with (a),
for each letter `s'` in `{a'^(+-1), b'^(+-1)}` with matching `s` in `S`:

```text
||(1-P) s' P|| < 2 eps',        ||P s' P - phi(s)|| < 2 eps'.
```

**Verification of (C1)-(C3).**
- **(C1).** Both off-diagonal blocks of `a'` are `< 2 eps'`: the lower one directly, and the upper one
  because `P a' (1-P) = ((1-P) a'^* P)^*`. So `||[P, pi_F(a)]|| < 2 eps' < eps`, and likewise for `b`.
- **(C2).** For `r` of length `m <= 34`, (K1) and a product estimate over contractions give
  `||P pi_F(r) P - r(A, B)|| <= (m-1) 2 eps' + m 2 eps' < 136 eps'`. So
  `||P(pi_F(r) - 1)P|| < eps/2 + 136 eps/300 < eps`.
- **(C3).** By (L0c) we have, say, `||A - 1|| >= sqrt 2`. Then
  `||P(pi_F(a) - 1)P|| >= sqrt 2 - 2 eps' > 1`. If instead `B != 1`, the same holds with `sqrt 3`.

So `(F, pi_F, P)` is an `eps`-corner, with `rank P = n`.

**Regular form.** Every irreducible representation of `F` occurs in the left regular representation
`lambda_F`. So `pi_F (+) rho` is isomorphic to `(n+k) lambda_F` for some `rho`. Replacing `P` by
`P (+) 0` changes no commutator or compression, so the corner survives inside a multiple of `lambda_F`.
This proves (1 => 3) and the first quantitative form.

## Step 3. Theorem B: averaging a corner over F

Let `(F, pi, P)` be an `eps`-corner and `d = diam F >= 1`. Suppose, for a contradiction, that
`d eps < 1/18`.

1. **Every group element almost commutes with `P`.** Each `g` in `F` is a word of length `<= d` in
   `a^(+-1), b^(+-1)`. By the Leibniz rule `[P, UV] = [P, U] V + U [P, V]`, Step 0 and (C1),
   `||pi(g) P pi(g)^* - P|| = ||[pi(g), P]|| <= d eps`.
2. **Average.** Put `E = |F|^(-1) sum_g pi(g) P pi(g)^*`. It is self-adjoint, commutes with `pi(F)`,
   and satisfies `||E - P|| <= d eps < 1/18`. So its spectrum lies within `d eps` of `{0, 1}`, which is
   within `d eps` of the spectrum of `P`.
3. **Round.** Let `Q = 1_[1/2, infinity)(E)`. It is a projection commuting with `pi(F)`, with
   `||Q - E|| <= d eps`, so `||Q - P|| <= 2 d eps < 1/9`. Let `sigma` be the restriction of `pi` to
   `ran Q`, a unitary representation of `G0` with finite image.
4. **Compare compressions.** For any `Y` with `||Y|| <= 2`,
   `||Q Y Q - P Y P|| <= ||(Q - P) Y Q|| + ||P Y (Q - P)|| <= 4 ||Q - P|| <= 8 d eps`. Hence:
   - with `Y = pi(r) - 1`, `D(sigma) <= eps + 8 d eps <= 9 d eps < 1/2`;
   - with `Y = pi(a) - 1` or `pi(b) - 1`, (C3) gives `||sigma(s) - 1|| >= 1 - 8 d eps > 1/2` for
     `s = a` or `s = b`. So `Q != 0` and `sigma` is nontrivial.
5. **Contradiction.** Decompose `sigma` into irreducibles. Since `D` of a direct sum is the maximum over
   the summands, some nontrivial irreducible constituent `tau` has `D(tau) <= D(sigma) < 1/2`, and
   `tau` has finite image. Item 2 of `lie-closure-trichotomy-without-finite-quotients` applies to
   `Gamma0 = G0` with `R = {r_1, r_2, r_P}`. Its instance table gives (H1) from
   `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes` and (H2) because `T` is infinite simple, with
   `eta_0 = min(1/2, 2 sin(pi/12)) = 1/2`. Item 2 says that `D(tau) >= eta_0 = 1/2` when the image is
   finite. This is a contradiction.

So `d eps >= 1/18` for every `eps`-corner, i.e. `c(F) >= 1/(18 diam F)`.

**Logarithmic-diameter families.** If `diam F <= C log |F|`, then `C log |F| >= 1/(18 eps)`, that is,
`|F| >= exp(1/(18 C eps))`.

## Remarks on scope

- Step 1 does not use that `F` is finite. Any unitary representation of any group generated by elements
  of order dividing 4 and 3 would do. Finiteness is what Step 2 supplies, and what Step 3 needs.
- Step 2 does not control `k`, the size of the padding, or `|F|`. This is Willett's Remark 1.13 ("no
  control on the size of the auxiliary representation θ"). Theorem B is the first lower bound on the
  size, and it holds for every corner, not only for those produced by Step 2.
- **Which half of the presentation is used.**
  - Step 2 (MF gives corners) uses the criterion in the direction "MF gives small nontrivial pairs". That
    direction is the contrapositive of the verified half, so it needs only that `alpha, beta` generate `T`
    and that the relators hold in `T`.
  - Step 1 (corners give MF) uses the other direction, which needs the completeness of the Lochak--Schneps
    presentation (`thompson-t-lochak-schneps-presentation`).
  - Step 3 uses item 2 of the trichotomy, through (H1) and (H2).
