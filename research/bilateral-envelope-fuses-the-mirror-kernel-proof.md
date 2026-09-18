---
rg: 2
id: bilateral-envelope-fuses-the-mirror-kernel-proof
kind: route
title: Swap the two boundary sites by a finitary involution, read the mirror head as a conjugate of the head, and let the kernel of a character swallow the simple finitary group
target: bilateral-envelope-fuses-the-mirror-kernel-with-the-head
requires:
  - jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group
---

Notation as in the target and in `jacobson-toeplitz-extension-is-a-mirror-quotient-of-a-lef-group`. Everything below
is elementary. The only imported facts are:
- the mirror embedding `P -> H_bi`, `(g,h) |-> g (+) h`, with `pr : P -> E_+` having kernel `1 x L_-` (MQ2, MQ3);
- simplicity of `GL_m(F_2) = SL_m(F_2)` for `m >= 3`, which is also used there.

## Step 1. Characters and their kernels

**(K1) Limits of approximations are characters.** Let `G` be a group and `rho_k : G -> U(d_k)` maps with
`||rho_k(gh) - rho_k(g) rho_k(h)||_2 -> 0` for all `g, h`. Here `||x||_2 = tr(x^* x)^(1/2)` with the normalized trace
`tr`. Permutation matrices are the sofic case, where `tr` is the fixed-point proportion. Fix an ultrafilter `omega` and
put `tau(g) = lim_omega tr rho_k(g)`. Then `tau` is a character.
- **Normalization.** `rho_k(1)^2 - rho_k(1) -> 0` and `rho_k(1)` is unitary, so `rho_k(1) -> 1` in `||.||_2`. Hence
  `tau(1) = 1`.
- **Inverses.** `rho_k(g^(-1)) rho_k(g) -> 1`, so `rho_k(g^(-1)) - rho_k(g)^* -> 0`.
- **Positive definite.** For `g_1..g_r` and scalars `a_i`, the sum `sum_(i,j) conj(a_i) a_j tau(g_i^(-1) g_j)` is the
  `omega`-limit of `tr(X_k^* X_k) >= 0`, where `X_k = sum_j a_j rho_k(g_j)`. This uses the two previous bullets and
  `|tr(y)| <= ||y||_2`.
- **Conjugation invariant.** `rho_k(h g h^(-1)) - rho_k(h) rho_k(g) rho_k(h)^* -> 0`, and `tr` is a trace.

**(K2) The kernel of a character.** Let `tau` be a character of `G` with GNS triple `(pi, H, xi)`, so that
`tau(g) = <pi(g) xi, xi>`. Put `N_tau = {g : tau(g) = 1}`.
- For `g` in `N_tau`: `||pi(g) xi - xi||^2 = 2 - 2 Re tau(g) = 0`, so `pi(g) xi = xi`. Hence, for every `h`,
  `tau(g h) = <pi(h) xi, pi(g^(-1)) xi> = tau(h)`.
- So `N_tau` is a subgroup. It is closed under products by the displayed identity, and closed under inverses because
  `tau(g^(-1))` is the complex conjugate of `tau(g)`.
- It is normal, by conjugation invariance.
- `tau` is constant on the cosets of `N_tau`.

## Step 2. (F1) The fusion

In `W`, the element `(w,1)` of `H_bi` is `1 + e_(0,1) (x) e_(0,3)^*`.
- On `V_+`, `Q = 1 - ST` is the projection onto `e_0`, because `T e_0 = 0` and `ST e_k = e_k` for `k >= 1`.
- `w - 1 = Q e_13` sends the third coordinate through `Q` into the first.

In the mirror basis `e'_k = e_(-1-k)`, the same computation gives that `(1,w')` is `1 + e_(-1,1) (x) e_(-1,3)^*`.

The involution `c` swaps `e_(0,i)` and `e_(-1,i)`. So

```text
c (1 + e_(-1,1) (x) e_(-1,3)^*) c^(-1) = 1 + c e_(-1,1) (x) (e_(-1,3)^* o c^(-1)) = 1 + e_(0,1) (x) e_(0,3)^*.
```

- **The two heads.** So `c (1,w') c^(-1) = (w,1)`, with `(1,w')` in `1 x L_-`.
- **The head is not in the kernel.** `(w,1)` is not in `1 x L_-`, because its first coordinate is `w != 1`.
- **Where the swap lives.** `c` is a finitary permutation, so `c` lies in `GL_fin(W) <= H_bi`. It is not in `P`: it
  does not preserve `V_+`.

## Step 3. (F2) Characters of H_bi

`GL_fin(W)` is the directed union of the groups `GL(U) = SL(U)`, for `U` spanned by finitely many basis vectors. Each
of these is simple once `dim U >= 3`, so `GL_fin(W)` is simple:
- take a nontrivial normal subgroup `N`, and some `g != 1` in `N ∩ GL(U_0)`;
- for every `U ⊇ U_0` with `dim U >= 3`, the subgroup `N ∩ GL(U)` is normal in `GL(U)` and nontrivial, hence equal to
  `GL(U)`;
- taking the union, `N = GL_fin(W)`.

Now let `tau` be a character of `H_bi` and `g != 1` in `GL_fin(W)` with `tau(g) = 1`.
- By (K2), `N_tau ∩ GL_fin(W)` is a nontrivial normal subgroup of `GL_fin(W)`, so it is all of `GL_fin(W)`.
- By (K2) again, `tau` is constant on cosets of `GL_fin(W)`, so it factors through `H_bi / GL_fin(W) = EL_n(A)`.

## Step 4. (F3) Descended characters

Let `chi` be a character of `E_+`, and suppose `chi o pr = tau|_P` for a character `tau` of `G = <P, c>`.
- `tau(1,w') = chi(1) = 1`, so `(1,w')` lies in `N_tau`.
- `N_tau` is normal in `G` and `c` is in `G`, so `(w,1) = c (1,w') c^(-1)` lies in `N_tau`.
- `L_+ x 1` lies in `P`, since its symbol is `1`. It is simple (Step 3 applied to `V_+`), and `N_tau ∩ (L_+ x 1)` is
  normal in it and contains `(w,1) != 1`. So `L_+ x 1 <= N_tau`.
- Hence `chi = 1` on `pr(L_+ x 1) = L`, the finitary kernel of `E_+ -> SL_n(A)`. So `chi` is `1` on `L` and, by (K2),
  it factors through `E_+ / L = SL_n(A)`.

A character of `H_bi` restricts to one of `G`, so the `H_bi` case is included.

**Converse.** For a character `psi` of `SL_n(A)`, pull it back along `H_bi -> EL_n(A)`. The result is a character of
`H_bi`. Its restriction to `P` is `(g,h) |-> psi(pi_+(g))`, which is `(psi o pi_+) o pr`.

## Step 5. (F4) Approximations

Let `rho_k : G -> U(d_k)` be asymptotically multiplicative, with `tr rho_k(1,w') -> 1`. Fix any ultrafilter `omega`.
- By (K1), `tau = lim_omega tr rho_k` is a character of `G` with `tau(1,w') = 1`.
- By Step 4, `N_tau` contains `L_+ x 1` and the `P`-normal closure of `(1,w')`. By Step 3 applied to `V_-`, that
  closure is `1 x L_-`.
- So `tau = 1` on `L_+ x L_-`.

This holds for every `omega`, so `tr rho_k(g) -> 1` for every `g` in `L_+ x L_-`. In particular it holds for every lift
`(w, l)` of the head.

- **Every descent is blind to the head.** Any `sigma_k(x) = rho_k(lift(x))` on `EL_n(J)` has `tr sigma_k(w) -> 1`. So
  it is not a sofic or hyperlinear approximation, and it does not separate `w`.
- **Families covered.** If `rho_k` is defined on all of `H_bi`, restrict it to `G`. This covers LEF local embeddings of
  `H_bi` composed with any representation of the finite groups, and every sofic or hyperlinear approximation of
  `H_bi`.

## Step 6. (F5) The rank invariant for linear models

Let `sigma : P -> GL_m(F_2)` be multiplicative on a set containing `1`, `x = (w,1)` and `x' = (1,w')`.
- **Both images are involutions.** `sigma(1)^2 = sigma(1)`, and `sigma(1)` is invertible, so `sigma(1) = 1`. The two
  heads square to `1` in `P`, since `x_13(r)^2 = x_13(2r) = 1`. So `sigma(x)^2 = sigma(x')^2 = 1`.
- **Conjugacy of involutions over `F_2`.** For an involution `g`, the matrix `N = g - 1` satisfies `N^2 = g^2 + 1 = 0`.
  So its Jordan form has `rank N` blocks of size `2` and `m - 2 rank N` blocks of size `1`. Two involutions of
  `GL_m(F_2)` are conjugate iff their `N` are conjugate, that is, iff `rank(g - 1)` agrees.
- **Equal ranks give equal traces.** If `rank(sigma(x) - 1) = rank(sigma(x') - 1)`, then `sigma(x)` and `sigma(x')` are
  conjugate. Then `tr pi sigma(x) = tr pi sigma(x')` for every homomorphism `pi` into `U(d)` or `Sym(d)`.
- **Periodic and window models.** A periodic or finite-window compression of `H_bi` represents `(w,1)` and `(1,w')` by
  the same finitary transvections of `W`, each with `rank(. - 1) = 1`.
- **Consequence.** For a descent one needs `tr pi sigma(x') -> 1` and `tr pi sigma(x) -> 0`. Neither survives equal
  ranks.

## Step 7. Why this is the whole class, and what is left

Every construction listed in the target factors its trace through a character of `<P,c>` (Step 5), or through a finite
linear group in which the two heads have equal rank (Step 6).

The surviving requirement is the character `1_(L_-)` on `P`. It is not the restriction of any character of `<P, c>`.
So a positive answer for `EL_n(J)` must come from approximations of `P` that are not restrictions from the LEF envelope,
and in linear form they must break the rank symmetry between the two boundary sites.

This matches the orientation obstruction met by the path-permutation criterion in `binary-jacobson-el3-is-sofic`. There
the constants detect the orientation of the turn at index `0`. Here the character must detect which side of the
boundary `0 | -1` a transvection sits on, and the finitary swap `c` is exactly what erases that.
