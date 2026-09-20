---
rg: 2
id: thompson-v-unitaries-generate-cuntz-algebra-proof
kind: route
title: Transposition projections cut out a full Cuntz corner, and four V-translates of that corner sum to an invertible element
target: thompson-v-unitaries-generate-cuntz-algebra
requires: []
---

This proof is self-contained. It uses only the Cuntz relations. Simplicity of `O_2` is
never used. Notation is that of the target. Two words are **incomparable**, written
`gamma _|_ delta`, when neither is a prefix of the other. Then `s_gamma^* s_delta = 0`.

## Step 0. The embedding

The code pairs of `g` can be refined, and
`s_q s_p^* = s_{q0} s_{p0}^* + s_{q1} s_{p1}^*`, so `u_g` does not depend on the chosen
pair. For a complete prefix code, `sum_i s_{p_i} s_{p_i}^* = 1`, so `u_g` is unitary.
Given `g, h`, refine their pairs so that the range code of `h` is the domain code of `g`.
Then `u_g u_h = u_{gh}`. This is the standard embedding of Birget and Nekrashevych. We use
only the formula.

## Step 1. Transposition projections

Let `alpha _|_ beta`. Let `t` be the element of `V` that swaps the cones of `alpha` and
`beta` and fixes a complete prefix code of the complement. Such a code exists because every
clopen set is a finite union of cones. Then

```text
1 - u_t = (s_alpha - s_beta)(s_alpha - s_beta)^* .
```

So with `y_{alpha,beta} = s_alpha - s_beta`, we have `y y^* in B`. Moreover
`v_{alpha,beta} = y/sqrt 2` is an isometry, because `y^*y = 2`, and
`E_{alpha,beta} = v v^* = (1 - u_t)/2` is a projection in `B`.

## Step 2. One full corner lies in B

Fix `alpha = 00`, `beta = 1`, `y = s_00 - s_1`, `v = y/sqrt 2`, `E = v v^*`. The map
`phi(x) = v x v^*` is an isometric *-isomorphism of `O_2` onto `E O_2 E`. So

```text
A = { x in O_2 : v x v^* in B }
```

is a C*-subalgebra of `O_2`, and `1 in A` because `E in B`.

Let `gamma, delta` be any words, possibly empty. The cones of `00gamma` and `1delta` are
disjoint, so Step 1 applies to `z = s_{00gamma} - s_{1delta}`, and `z z^* in B`. The cross
terms vanish, so

```text
y^* z = s_00^* s_{00gamma} - s_00^* s_{1delta} - s_1^* s_{00gamma} + s_1^* s_{1delta} = s_gamma + s_delta .
```

Hence

```text
(y y^*)(z z^*)(y y^*) = y (y^*z)(y^*z)^* y^* = 2 phi( (s_gamma + s_delta)(s_gamma + s_delta)^* )
```

lies in `B`, and so `(s_gamma + s_delta)(s_gamma + s_delta)^* in A`.

- **Diagonal projections.** With `gamma = delta` this gives `4 s_gamma s_gamma^*`, so
  `s_gamma s_gamma^* in A` for every word.
- **Symmetric pairs.** Subtracting the two diagonal terms gives
  `s_gamma s_delta^* + s_delta s_gamma^* in A`.
- **Off-diagonal matrix units.** If `gamma _|_ delta`, right multiplication by
  `s_delta s_delta^*` gives `s_gamma s_delta^*`, because `s_gamma^* s_delta = 0`. So
  `s_gamma s_delta^* in A` whenever `gamma _|_ delta`.
- **The generators.** The following products and sums have every factor off-diagonal:

  ```text
  s_0 = s_00 s_0^* + s_01 s_1^* = (s_00 s_1^*)(s_1 s_0^*) + s_01 s_1^* ,
  s_1 = s_10 s_0^* + s_11 s_1^* = s_10 s_0^* + (s_11 s_0^*)(s_0 s_1^*) .
  ```

  So `s_0, s_1 in A`.

Hence `A = O_2`, that is, `E O_2 E = v O_2 v^* <= B`.

## Step 3. Translate the corner

Consider the four incomparable pairs `(alpha_i, 1)` with
`alpha_i in {00, 01, 000, 001}`. For each `i`, let `g_i in V` send cone `00` to cone
`alpha_i` and cone `1` to itself, and map the complement onto the complement:

| `i` | `g_i` |
|---|---|
| `01` | `00 -> 01`, `01 -> 00`, `1 -> 1` |
| `000` | `00 -> 000`, `010 -> 001`, `011 -> 01`, `1 -> 1` |
| `001` | `00 -> 001`, `010 -> 000`, `011 -> 01`, `1 -> 1` |
| `00` | `g = 1` |

Then `u_{g_i} s_00 = s_{alpha_i}` and `u_{g_i} s_1 = s_1`. So with
`v_i = (s_{alpha_i} - s_1)/sqrt 2` we have `v_i = u_{g_i} v`. For all `i, j`,

```text
v_i O_2 v_j^* = u_{g_i} ( v O_2 v^* ) u_{g_j}^*  <=  B .
```

## Step 4. The four corners fill O_2

Let `h = sum_i v_i v_i^*`, which lies in `B`. We show `h >= 1/400` in every representation
of `O_2` on a Hilbert space. Fix a unit vector `x`. Put `eps^2 = <h x, x>`, so
`sum_i ||(s_{alpha_i}^* - s_1^*) x||^2 = 2 eps^2`, and put `xi = s_1^* x`.

1. **Each piece is close to `xi`.** `||s_{alpha_i}^* x - xi|| <= sqrt 2 eps` for each `i`.
2. **`xi` is almost fixed by both adjoints.** `s_000^* x = s_0^* s_00^* x`, so
   `||s_0^* xi - xi|| <= ||s_0^*(xi - s_00^* x)|| + ||s_000^* x - xi|| <= 2 sqrt 2 eps`.
   Likewise, using `s_001^* x = s_1^* s_00^* x`, we get `||s_1^* xi - xi|| <= 2 sqrt 2 eps`.
3. **`xi` is small.** `||xi||^2 = ||s_0^* xi||^2 + ||s_1^* xi||^2`. If
   `||xi|| > 2 sqrt 2 eps`, step 2 gives `||xi||^2 >= 2(||xi|| - 2 sqrt 2 eps)^2`, and so
   `||xi|| <= 4 eps/(sqrt 2 - 1) < 10 eps`. In either case `||xi|| < 10 eps`.
4. **`x` is small.** `1 = ||x||^2 = ||s_00^* x||^2 + ||s_01^* x||^2 + ||s_1^* x||^2`, and
   each term is at most `(||xi|| + sqrt 2 eps)^2 < (11.5 eps)^2`. So `eps^2 > 1/400`.

Hence `h >= 1/400`. So `h` is invertible, and `h^{-1} in B`. For any `x in O_2`,

```text
x = h (h^{-1} x h^{-1}) h = sum_{i,j} v_i [ v_i^* h^{-1} x h^{-1} v_j ] v_j^*  in  sum_{i,j} v_i O_2 v_j^*  <=  B .
```

So `B = O_2`. QED.

## The consequences listed in the target

- **Images.** A unital *-homomorphism maps `C*(u_V)` onto `C*(theta(u_V))`.
- **Infiniteness.** For `C != 0`, `theta(s_0)^* theta(s_0) = 1`, and
  `theta(s_0) theta(s_0)^* = 1 - theta(s_1) theta(s_1)^*`. Here
  `theta(s_1) theta(s_1)^*` is a projection, and it is nonzero because
  `theta(s_1)^* theta(s_1) = 1`. So `1` is an infinite projection.
- **Consequences of infiniteness.** Every MF algebra is stably finite (Blackadar--Kirchberg).
  Every unital quasidiagonal algebra is stably finite. An algebra with an infinite unit is
  neither.
- **The listed representations.**
  - **Orbit representation.** Let `s_i e_eta = e_{i eta}` on `l^2` of an orbit. This is a
    Cuntz family, and `u_g e_eta = e_{g eta}`.
  - **Bernoulli Koopman representation.** Let `(s_i f)(x) = sqrt 2 * 1_{C_i}(x) * f(sigma x)`
    on `L^2` of the uniform Bernoulli measure. This is a Cuntz family, and `u_g` is the
    Radon--Nikodym-twisted Koopman unitary.
  - **Fock representation.** Let `S_i e_w = e_{iw}` on `l^2` of the finite words. This is a
    Toeplitz--Cuntz family whose defect `1 - S_0 S_0^* - S_1 S_1^*` has rank one, so it is a
    Cuntz family modulo compacts.
