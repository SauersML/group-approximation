---
rg: 2
id: kms-hc1-witt-carry-syzygy-lifts-by-right-freeness-proof
kind: route
title: The b-linear part of the ca-edge algebra is a smash product V (x) u(h), free on the right, so Tor_1 vanishes and every seed syzygy is a combination of relator multiples with right contexts that kill m0
target: kms-hc1-witt-carry-syzygy-lifts-by-right-freeness
requires: [kms-hc1-ca-edge-defect-is-a-witt-carry-syzygy, kms-hc1-witt-carry-syzygy-kassel-coordinate-vanishes, kms-hc1-edge-s-pair-jumps-are-affine-coroot-p-power-relations]
artifacts:
  - experiments/kms-hc1-syzygy-lift-2026-09-18/lift_check.py
  - experiments/kms-hc1-syzygy-lift-2026-09-18/lift_p11.out
  - experiments/kms-hc1-syzygy-lift-2026-09-18/lift_p13.out
---

Notation of the claim. `U = u(h)` is a cocommutative Hopf algebra, with
`a`, `c` and `e` primitive. Write `Delta(u) = sum u_(1) (x) u_(2)` and `S`
for the antipode.

## 1. Right freeness (F)

For a `U`-bimodule `X` and `x` in `X`, put
`ad(u)(x) = sum u_(1) x S(u_(2))`. Then `ad(uv) = ad(u) ad(v)`, and
`ad(u)(k)` lies in `K` for `k` in `K`, because `K` is a sub-bimodule. For
primitive `a`, `ad(a)(x) = ax - xa`. So in `B`

```text
ad(a)^2 b = a^2 b - 2 a b a + b a^2 = -s1,
ad(c)^2 b = c^2 b - 2 c b c + b c^2 =  s2.
```

**The map psi.** Define `psi : U (x) U -> B/K` by
`psi(u (x) w) = ad(u)(b) w`. For `u = u' a^2` we get
`ad(u)(b) = ad(u')(-s1)`, which is in `K`. The case `u' c^2` is the same.
So `psi` factors through `V (x) U`, with `V = U/(Ua^2 + Uc^2)`.

`psi` is surjective. The identity
`x b y = sum ad(x_(1))(b) x_(2) y` holds for `x` in `U`: expand
`ad(x_(1))(b) x_(2) = x_(1) b S(x_(2)) x_(3)` and use
`sum S(x_(1)) x_(2) = eps(x)`.

**The map phi.** Let `V (x) U` be the bimodule with the right action
`(v (x) w) y = v (x) wy` and the left action
`u (v (x) w) = sum u_(1) v (x) u_(2) w`. This is a bimodule, because
`Delta` is an algebra map. Put `v0 = 1 mod (Ua^2+Uc^2)` and define
`phi : B -> V (x) U` by `phi(x b y) = x (v0 (x) 1) y`. Then

```text
phi(s1) = 2 a(v0(x)1)a - (v0(x)1)a^2 - a^2(v0(x)1)
        = 2(av0(x)a + v0(x)a^2) - v0(x)a^2 - (a^2v0(x)1 + 2av0(x)a + v0(x)a^2)
        = -a^2 v0 (x) 1 = 0.
```

In the same way, `phi(s2) = c^2 v0 (x) 1 = 0`. So `phi` factors through
`B/K`.

**Composition.** `phi(ad(u)(b)) = sum u_(1)(v0(x)1)S(u_(2))`. This equals
`sum u_(1) v0 (x) u_(2) S(u_(3))`, which is `u v0 (x) 1`. Hence
`phi psi (u v0 (x) w) = u v0 (x) w`, so `phi psi = id`. Since `psi` is onto,
`psi` is an isomorphism `V (x) U -> B/K` of right `U`-modules. So `B/K` is
right-free, with basis `ad(u_i)(b)` for any lift `u_i` of a basis of `V`.
All of this respects the `(a,c)`-multidegree. QED (F).

## 2. The right-context lift (L)

Apply `- (x)_U F_p` (right tensor with the trivial module) to
`0 -> K -> B -> B/K -> 0`:

```text
Tor_1^U(B/K, F_p) -> K (x)_U F_p -> B (x)_U F_p -> (B/K) (x)_U F_p -> 0.
```

The first group is 0 by (F). Also `K (x)_U F_p = K/K U^+ = K/K+`, and
`B (x)_U F_p = U` by `x (x) y -> x eps(y)`. So

```text
pi : K/K+ -> U,   pi(u s1 v) = -eps(v) u a^2,   pi(u s2 v) = eps(v) u c^2,
```

is injective. For a syzygy, `R = U1 s1 + U2 s2` lies in `K`, and
`pi(R) = -U1 a^2 + U2 c^2 = 0`. So `R` lies in `K+`. QED (L).

As elements of `B`,
`R = U1(2a(x)a - 1(x)a^2) + U2(1(x)c^2 - 2c(x)c)`. The terms
`-U1a^2(x)1 + U2c^2(x)1` cancel exactly in `U (x) U`. So `R` is the image of
the non-`b`-ending part of `U1 f0_210 + U2 f0_012`.

## 3. The lift to I (Z)

Fix a syzygy `(U1,U2)` of multidegree `(p-2,0,p)` and `(p,0,p-2)`. Choose
PBW-word lifts of `U1` and `U2` to `F<<Y_a,Y_c>>`. By (L), in `B`,

```text
R = sum_j u_j s_(i_j) v_j,   v_j homogeneous in U^+.
```

Lift `u_j` and `v_j` to words in `Y_a, Y_c`, with every `v_j` of positive
degree. The identity then holds in `F<<a,c>> b F<<a,c>>` modulo
`E b F + F b E`. Also `U1 a^2 - U2 c^2` lies in `E`. Each element of `E` is
a sum `sum x g0 y` of lowest forms `g0` of ca-edge group relators `g`,
which are elements of `I` in `Y_a, Y_c` only. So there is `T` in `I` of the
form

```text
T = U1 f_210 + U2 f_012 - sum_j u_j f_(i_j) v_j - sum_l x_l g_l y_l,
```

where each `x_l` or `y_l` contains exactly one `Y_b`, and
`U1 f0_210 + U2 f0_012 - sum u_j f0 v_j - sum x_l g0_l y_l = 0` in degree
`2p+1`.

**Degrees.** Each relator involves two letters. By the torus lemma (the
torus `(F_p^*)^3` acts on `A`, Attempt 5 of
`kms-hc1-a2-pro-p-completion-is-iwahori-criterion`), each eigencomponent
`f` has components only in degrees `d + k(p-1)`. Each summand of `T` is a
homogeneous word, times an eigencomponent, times a homogeneous word, with
lowest part in degree `2p+1`. So `T` lives in degrees `2p+1+k(p-1)`. The
`k=0` part is 0, so every component of `T` has degree at least `3p`. The
degree-`3p` part is the sum of the first-order tails:

```text
D = U1 f1_210 + U2 f1_012 - sum_j u_j f1_(i_j) v_j - sum_l x_l g1_l y_l.
```

**Value.** Here `rho` is multigraded, `gr I` lies in `ker(A -> u(L_p))`
(since `Gamma^` maps onto `I_1`), and in the truncated `u(N)` the kernel
of `u(N) -> u(L_p)` in degree `3p` is `F z`, which sits in `(p,p,p)`. So
`rho(D) = zeta z`, where `zeta` is read off the `(p,p,p)`-component `D'` of
`D`. Evaluate `rho(D') m0` in `M = u(N)/u(N)H^+`:

- `g1_l` involves only `Y_a, Y_c`, so `x_l g1_l y_l` has `b`-degree 1. It
  has no `(p,p,p)` component.
- The `(p,p,p)` component of `u_j f1 v_j` uses the `(2,p,0)` or
  `(0,p,2)` part of `f1`. Since `v_j` is a positive-degree word in
  `Y_a, Y_c`, `rho(v_j)` lies in `u(H)^+`, which kills `m0`. So its
  contribution is 0.
- `U1 f1_210` contributes `rho(U1) X_210`, and `U2 f1_012` contributes
  `rho(U2) X_012`. Here `rho(U_i)` lies in `u(H) = U`, so it depends only
  on the class of `U_i`.

Hence `zeta z m0 = (U1 X_210 + U2 X_012)_z`, and `zeta = zeta(U1,U2)`.

**Membership in gr I.** The value computation above is an identity for `D`,
whether or not `D` is 0. For `sigma` it gives `zeta = 6 alpha_B`, which is
nonzero for `alpha_B != 0`, so `D != 0` and `D = T_low` lies in `gr I`. For
any other syzygy with `D = 0` the value is 0 and nothing is claimed.
The components of `D` outside `(p,p,p)` have degree `3p` and lie in `ker(A -> u(L_p))`, because
that kernel is multigraded. By (R1) of
`kms-hc1-edge-s-pair-jumps-are-affine-coroot-p-power-relations`, which uses
Open 1, they lie in `J+Z`, and `J+Z` lies in `gr I`. So `D'` lies in
`gr I`. QED (Z).

## 4. (E_p)

`T_sigma` has row `(0,0,6)` by (K) of
`kms-hc1-witt-carry-syzygy-kassel-coordinate-vanishes`. Its rotations have
rows `(-6,-6,-6)` and `(0,6,0)` by (T) of
`kms-hc1-ca-edge-defect-is-a-witt-carry-syzygy`, and the determinant is
`-216`. So `V` has dimension at least 3. Since `dim W <= 3`, `V = W`. QED.

This does not need to know that each slice has one visible jump. Nor does
it need the values `zeta(e_k)` of the other syzygies.

## 5. Exact checks

`lift_check.py p` builds `U` from the PBW product rule
`a^n c^j = sum_r (-1)^r r! C(n,r) C(j,r) c^(j-r) e^r a^(n-r)` with
exponents `>= p` set to 0. It works in `B` at `(a,c)`-multidegree `(p,p)`
and eliminates exactly over `F_p`.

| p | dim B(p,p) | gens K+ | rank K+ | (F) | sigma, e_k in K+ | controls |
|---|---|---|---|---|---|---|
| 5 | 174 | 158 | 136 | 34 = 34 | yes | outside |
| 7 | 510 | 582 | 454 | 50 = 50 | yes | outside |
| 11 | 2320 | 3242 | 2228 | 82 = 82 | yes | outside |
| 13 | 4146 | 6118 | 4036 | 98 = 98 | yes | outside |

The controls are `(c^2 e^(p-2), 0)` and the half-syzygy `3 e_(p-2)` alone.
Their `R` has `pi(R) != 0`, so it cannot lie in `K+`. The program confirms
this, which calibrates the membership test.
