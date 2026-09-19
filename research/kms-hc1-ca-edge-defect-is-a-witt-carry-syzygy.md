---
rg: 2
id: kms-hc1-ca-edge-defect-is-a-witt-carry-syzygy
kind: claim
title: The first Kassel direction of the A~2 Iwahori holds for p=11, and for every p it reduces to one scalar, because the ca-edge jump is an explicit Witt-carry syzygy with restricted part 6 h_B and the other two edge jumps are its rotations
distinct_from:
  kms-hc1-edge-s-pair-jumps-are-affine-coroot-p-power-relations: that claim computes the three edge jumps for p=5,7 by storing t-parts in u(N_alpha), proves the reduction (R1)-(R2) to their independence (E_p), and leaves (E_p) open for p >= 11. This claim computes the jumps exactly for p=11 by a dual method, proves (E_p) for p=11, and for every p reduces (E_p) to one congruence by a symbolic evaluation of the ca jump and a rotation lemma.
  kms-hc1-a2-pro-p-completion-is-iwahori-criterion: that claim states the criterion and the towers. This claim settles the n=1 case of its Open 2 for p=11 and reduces it for every p to a single scalar.
artifacts:
  - experiments/kms-hc1-kassel-dual-2026-09-18/fo_dual.cpp
  - experiments/kms-hc1-kassel-dual-2026-09-18/run_dual.sh
  - experiments/kms-hc1-kassel-dual-2026-09-18/syz_eval.py
  - experiments/kms-hc1-kassel-dual-2026-09-18/dual_p5.out
  - experiments/kms-hc1-kassel-dual-2026-09-18/dual_p7.out
  - experiments/kms-hc1-kassel-dual-2026-09-18/dual_p11.out
  - experiments/kms-hc1-kassel-dual-2026-09-18/pairs.out
---

Notation of `kms-hc1-edge-s-pair-jumps-are-affine-coroot-p-power-relations`
(below: the edge-jump claim).

- `A = F_p<<Y_a,Y_b,Y_c>>` and `I` is the relator ideal.
- `W = ker(A -> u(L_p))/(J+Z)` at multidegree `(p,p,p)`. It has dimension at
  most 3, by (R1) of the edge-jump claim.
- `N_(kappa,alpha)` is the Kassel extension `L_p + F z`, with cocycle
  `kappa * i delta_(i+j,p) tr(xy) z` and p-map
  `(h t)^[p] = h t^p + alpha(h) z`, for `alpha` a linear form on the Cartan
  subalgebra, `alpha_A = alpha(hA)` and `alpha_B = alpha(hB)`. The programs
  use `kappa = 1`. The coordinates `(v00, v10-v00, v01-v00)` of a jump are
  the coefficients of `(kappa, alpha_A, alpha_B)` in its value `zeta`.
- `(E_p)` says that the three edge jumps `S_ca`, `S_bc` and `S_ab` are
  independent in these coordinates. By (R2) of the edge-jump claim, given
  Open 1, `(E_p)` gives `gr I = ker(A -> u(L_p))` through degree `3p`. That
  is the `n=1` case of Open 2 of `kms-hc1-a2-pro-p-completion-is-iwahori-criterion`.

## Results

| part | statement | status |
|---|---|---|
| (D) | a dual evaluation of the t-parts makes `p=11` computable | exact method, soundness argued as in (F2) of the edge-jump claim |
| (P11) | `S_ca=(0,0,-1)`, `S_bc=(0,1,0)`, `S_ab=(-1,-1,-1)` at `p=11`, so `(E_11)` holds | exact computation |
| (S) | the ca jump is carried by the syzygy `sigma = 2e_(p-3)+3e_(p-2)`, the only one that uses `(Y_cY_a)^p` (the Witt carry) | proved for every `p` (the syzygy); the lift to `I` is argued |
| (A) | the restricted part of `zeta(sigma)` is `0*alpha_A + 6*alpha_B` for every `p >= 5` | proved, given the two seed t-parts (S0) |
| (T) | the rotation `a->b->c->a` carries the ca jump to the ab jump and the bc jump, with an explicit affine action on `(kappa,alpha)` | proved |
| (Red) | for every `p >= 5`: the rotated triple `T_sigma, tau T_sigma, tau^2 T_sigma` has independent values iff `k(p) != 2 mod p`, where `k(p)` is the Kassel coordinate of `zeta(sigma)`; this gives `(E_p)` | proved from (S), (A) and (T) |
| (K) | `k(p) = 0` for `p = 5, 7, 11, 13` | exact computation (p=13 from the seeds (S0), which are computed exactly at p=13) |

So `(E_p)`, and the `n=1` case of Open 2, holds for `p = 5, 7, 11`. It also
holds for `p = 13`, given the argued lift of (S). For every other `p` it is
equivalent to one scalar congruence, `k(p) != 2`. Equivalently,
the ca jump does not vanish on the rotation-invariant Kassel extension
`N_(1,-1/3,-1/3)`.

## (D) The dual method

`fo_dual.cpp` is `fo_sb.cpp` of the edge-jump claim, with one change. For the
edge `xy` with third letter `w`, let `H` be the 3-dimensional Heisenberg
subalgebra of `N` spanned by `rho(Y_x)`, `rho(Y_y)` and their bracket. Let
`M = u(N)/u(N)H^+`, with `m0` the class of 1, and let `psi(y)` be the
coefficient of the PBW monomial `z` in `y m0`.

Each t-part `X` is stored as the vector `X m0` in `M`, and only in the
multidegree `mu + (p-1)e_w` that can reach `(p,p,p)`. This is enough for
three reasons.

- Every jump `T` that lands in `(p,p,p)` lies in `ker(A -> u(L_p))`. So
  `rho(T) = zeta(T) z`, and any functional with `psi(z) = 1` reads off
  `zeta(T)`.
- The multigrading forces the context word `v` to the right of a t-part to be
  a word in `x` and `y`: the `w`-letter is used up. So
  `rho(v) m0 = eps(v) m0`.
- The updates are therefore `S(A,B) = A y - x B -> eps(y) w_A - rho(x) w_B`,
  and reduction by `c u E v` gives `w -= c eps(v) rho(u) w_E`.

At `(p,p,p)`, `M` has 195, 1311, 38623 and 179543 monomials for
`p = 5, 7, 11, 13`, against 1903, 18313, 900421 and 5098459 for `u(N)`. The
t^0 decisions are exact in `A`, as before. The sanity check (a jump below
degree `3p` must have `rho = 0`) passes in every run.

The method reproduces all nine values of the edge-jump claim at `p=5` and
`p=7` (`dual_p5.out`, `dual_p7.out`).

## (P11) The edge jumps at p=11 (exact)

`run_dual.sh 11` (`dual_p11.out`) runs 3 slices for 3 values of `alpha`, at
130-175 s each. Each slice has exactly one `rho`-visible jump, from degree 23
to degree 33. The jump is pure `z`, lands in `(11,11,11)`, and has 0 sanity
failures.

| edge | lead S-pair | `zeta` at `alpha=(0,0),(1,0),(0,1)` | coord |
|---|---|---|---|
| `ca` | `S((ca)^11 \| cacacab)` | `0, 0, 10` | `(0,0,-1)` |
| `bc` | `S((cb)^11 \| cbcba)` | `0, 1, 0` | `(0,1,0)` |
| `ab` | `S(cbab \| (ba)^11)` | `10, 9, 9` | `(-1,-1,-1)` |

These are the `p=5,7` rows again. The determinant is `-1`, which is not 0. So
`(E_11)` holds and, by (R2) of the edge-jump claim, `gr I = ker(A -> u(L_11))`
through degree 33.

The run at `p=13` needs about 1000 s of CPU per slice. It did not finish
within the 1200 s wall-clock limit on the shared machine, so it was stopped.

## (S) The ca jump is the Witt-carry syzygy (every p)

On the ca slice `(p,1,p)`, write `a = rho(Y_a) = E12`, `c = rho(Y_c) = E31 t`
and `e = ca - ac = E32 t`. They span `H`, and `u(H) = u(h)` is the restricted
Heisenberg algebra. It has PBW basis `c^j e^k a^i` with all exponents `< p`,
`e` central and `e^p = 0`. Since `a^i c = c a^i - i e a^(i-1)`,

```text
a^m c^2 = c^2 a^m - 2m c e a^(m-1) + m(m-1) e^2 a^(m-2).
```

Only two relator eigencomponents carry the letter `b` at the end of their
lowest forms. They come from the lowest Lie terms `[[Y_a,Y_b],Y_a]` and
`[[Y_b,Y_c],Y_c]`:

```text
f_[a,b,a]{210} = -Y_a^2 Y_b + (words ending in Y_a),
f_[b,c,c]{012} = +Y_c^2 Y_b + (words ending in Y_c).
```

Their t-parts in `M`, in multidegrees `(2,p,0)` and `(0,p,2)`, are:

> **(S0)** `X_210 = E23^(p-2) E13^2 m0` and `X_012 = -E23^(p-2) (E21 t)^2 m0`.

This is printed as `SEEDGEN` for `p = 5, 7, 11, 13` (`pairs.out`). It is the
degree-`(d+p-1)` component of the truncated-exponential commutator of
(H1) in the edge-jump claim. It is not derived here for general `p`.

A **u(h)-syzygy** of the two seeds is a pair `(U1,U2)` in `u(h)` with
`U1 a^2 = U2 c^2`. For such a pair, the program's formal mode (`SEEDS=1`)
tracks `zeta = psi(U1 X_210) + psi(U2 X_012)`.

In multidegree `(p,p)` of `(a,c)`, `u(h)` has basis
`v_k = c^(p-k) e^k a^(p-k)`, `k = 1..p-1`. Write
`U2 = sum_k g_k c^(p-2-k) e^k a^(p-k)`. Then

```text
U2 c^2 = sum_k g_k ( v_k - 2(p-k) v_(k+1) + (p-k)(p-k-1) v_(k+2) ),
```

where `v_p = e^p` is 0 in `u(h)`. The term `v_(p-1) = c e^(p-1) a` does not
lie in `u(h) a^2`. So `(U1,U2)` is a syzygy iff the coefficient of `v_(p-1)`
vanishes, that is `6 g_(p-3) = 4 g_(p-2)`. The syzygy space therefore has
this basis:

- `g = e_k` for `k <= p-4`. These never reach `v_p`.
- `sigma: g = 2e_(p-3) + 3e_(p-2)`. The `k=p-2` term produces
  `3 * 2 * v_p = 6 e^p`, and the syzygy uses `e^p = 0`.

In `A`, `e^p = 0` is the vertex relation `(Y_cY_a)^p - (Y_aY_c)^p`, modulo
the Serre words. That is the `(Y_cY_a)^p` in the ca lead S-pair, and it is
the p-th power, or Witt-vector carry, of the edge. For `sigma`,

```text
U2 = 2 c e^(p-3) a^3 + 3 e^(p-2) a^2,
U1 = 2 c^3 e^(p-3) a - 9 c^2 e^(p-2),     U1 a^2 = 2 v_(p-3) - 9 v_(p-2) = U2 c^2.
```

**Numerics.** `syz_eval.py` evaluates `zeta` on this basis from the pairing
tables (`PAIRTAB=1`). The values are these:

| p | `zeta(e_k)`, all `k <= p-4` | `zeta(sigma)` |
|---|---|---|
| 5  | (only `e_1`) `(0,0,0)` | `(0,0,1) = (0,0,6)` |
| 7  | `(0,0,0)` | `(0,0,6)` |
| 11 | `(0,0,0)` | `(0,0,6)` |

So on the ca slice the jump is `-1/6 zeta(sigma)`. At `p=5` and `p=7`,
`SEEDS=1` also recovers the program's actual jump: its seed cofactors
satisfy `U1 a^2 = U2 c^2`, and `sum psi(U_s X_s)` equals the jump
(`SEEDSUM ... OK`).

**Lift (argued).** Every u(h)-syzygy gives an element of `gr I` in
`(p,p,p)`, with value `zeta(U1,U2)`. The argument runs as follows.

1. Lift `U_i` to words in `Y_a`, `Y_c` and form
   `F = U1 f_210 + U2 f_012 - (ca-edge relator multiples)`. The subtracted
   terms cancel the `Y_b`-ending part `(-U1 a^2 + U2 c^2) Y_b`. This is
   possible because `U1 a^2 - U2 c^2` lies in the ca-edge relator ideal of
   `F<<Y_a,Y_c>>`, whose quotient is `u(h)`.
2. The remaining lowest part lies in `gr I` and ends in `Y_a` or `Y_c`. By
   (R1) of the edge-jump claim, `gr I = ker(A -> u(L_p))` in the degrees
   `< 3p` involved. So it decomposes into relator multiples with right
   contexts in `(Y_a,Y_c)`. Their t-parts are killed by `eps`, and the
   ca-relator t-parts leave the box.
3. What is left in degree `3p` is `sum psi(U_s X_s)` plus terms with `rho = 0`.

The steps checked by the program are step 1 and the value at `p=5,7`.

## (A) The restricted part of zeta(sigma), every p >= 5 (proved, given (S0))

`H` kills `m0`, so `psi(h_1...h_n Y m0) = psi(ad(h_1)...ad(h_n)(Y) m0)`. Here
`ad` acts as a derivation on the product `Y` in `u(N)`, factor by factor,
with no reordering.

In `(p,p,p)`, `alpha` enters `psi` only through `(hA t)^[p]` and
`(hB t)^[p]`. That needs `p` factors, each of the form `(x_i hA + y_i hB) t`.

- Reordering never creates such a term, because it lowers the number of
  factors, and `p` factors of total t-degree `p` each have t-degree 1.
- Cartan elements at `t^1` commute: the cocycle needs `i+j = p`, and here
  `i+j = 2`.
- The product expands as `prod(x_i hA + y_i hB)`. Mixed monomials
  `(hA t)^m (hB t)^(p-m)` are PBW monomials other than `z`. So:

> the `alpha_B`-coefficient is `sum over derivation paths of prod y_i`, and
> the `alpha_A`-coefficient is `sum of prod x_i`,

over the ways of turning every factor into `(Cartan) t` with one t-carrying
step each. The steps come from `c` and `e`; `a` carries no `t`.

The brackets needed are these:

- `ad(e)`: `E23 -> -hB t`, `E13 -> -E12 t`.
- `ad(a)`: `E23 -> E13`, `E13 -> 0`, `E21 t -> hA t`.
- `ad(c)`: `E13 -> -(hA+hB) t`, `E23 -> -E21 t`.

Any factor that meets a second t-carrying step, or a step that makes it
non-Cartan, has t-degree `>= 2` or stays off the Cartan. It contributes 0.

- `pi1(p-2) = psi(c^2 e^(p-2) X_210)`, with `X_210 = E23^(p-2) E13^2`. The
  `p-2` operators `e` go to the `p-2` factors `E23` (`(p-2)!` ways, each
  giving `y = -1`). The two `c` go to the two `E13` (2 ways, `y = -1`). The
  `alpha_B` part is `2 (p-2)! (-1)^p = -2`, by Wilson.
- `pi1(p-3) = psi(c^3 e^(p-3) a X_210)`. The `a` acts first. On an `E13` it
  gives 0, so it turns one of the `p-2` factors `E23` into `E13`. Then the
  `e` go to the other `p-3` factors `E23` (`(p-3)!` ways) and the `c` go to
  the three `E13` (6 ways). The `alpha_B` part is `-6 (p-2)(p-3)! = -6`.
- `pi2(p-2)` and `pi2(p-3)`, on `X_012 = -E23^(p-2) (E21 t)^2`. Each `E21 t`
  already has its `t`, so it must meet an `a`, and it becomes `hA t` with
  `y = 0`. So the `alpha_B` part is 0.
- `alpha_A`, all four pairings. At least `p-3 >= 2` factors `E23` pass
  through `e` and become `hB t`, with `x = 0`. So the `alpha_A` part is 0.

Hence `alpha`-part of
`zeta(sigma) = 2 pi1(p-3) - 9 pi1(p-2) + 2 pi2(p-3) + 3 pi2(p-2)` is

```text
0 * alpha_A + (2(-6) - 9(-2)) alpha_B = 6 alpha_B,
```

for every `p >= 5`. The tables give the same values: `alpha_B` parts
`pi1(p-2) = -2` and `pi1(p-3) = -6` at `p = 5, 7, 11`.

This is the closed form that the edge-jump claim's interpretation predicted:
the restricted part of the ca defect is the p-power relation of the coroot
`hB` of `delta - alpha_2 = [c,a]`, with the scalar `6 = 3!`. The `3!` counts
the three `E13` fed by `c`.

## (T) The rotation lemma (proved)

Let `pi` be the cyclic permutation `1 -> 2 -> 3 -> 1`, `Pi` its permutation
matrix (`Pi E_ij Pi^-1 = E_(pi i, pi j)`), and `Delta = diag(1,t,t)`. Put
`g = Delta Pi` and `tau = Ad(g)` on `sl3[t,t^-1]`. Then:

- `tau(E12) = E23`, `tau(E23) = E31 t` and `tau(E31 t) = E12`.
- `Ad(Delta) E_ij = t^(d_i - d_j) E_ij` with `d = (0,1,1)`. The only
  negative shifts are on `E12` and `E13`, whose `Pi`-preimages `E31` and
  `E32` occur in `L_p` only with a factor `t`. So `tau(L_p) = L_p`.
- `g^3 = t^2 I`, so `tau^3 = 1`.
- `tau` permutes the multidegrees `(a,b,c) -> (c,a,b)`. So it preserves the
  box `(p,p,p)` and passes to the truncation `N`.

On `A`, let `tau_A` be `Y_a -> Y_b -> Y_c -> Y_a`. It preserves `I`. The
relator set is rotation-symmetric, except for the orientation of the ca
relator, and the normal closures of `[[c,a],c]` and `[[a,c],c]` agree.

**Cocycle.** Write `omega(X,Y) = kappa Res(t^-p tr(X' Y) dt)`. Since `t^-p`
is a constant for `d/dt` in characteristic `p`, this is the Kassel cocycle
`kappa i delta_(i+j,p) tr(xy)`. From `(gXg^-1)' = g X' g^-1 + [g'g^-1, gXg^-1]`
and `g'g^-1 = D/t`, with `D = diag(0,1,1)`,

```text
omega(tau X, tau Y) = omega(X,Y) + kappa Res(t^(-p-1) tr(D tau[X,Y]) dt)
                    = omega(X,Y) + kappa lambda([X,Y]),
lambda(Z) = tr(S_pi Z_(p)),   S_pi = Pi^-1 D Pi = diag(1,1,0),
```

where `Z_(p)` is the diagonal `t^p`-coefficient of `Z`. `Ad(Delta)` fixes
diagonal matrices. So the defect is the coboundary of `lambda`, and

```text
Phi : N_(kappa,alpha') -> N_(kappa,alpha),   Phi(X) = tau X + kappa lambda(X) z,   Phi(z) = z,
```

is an isomorphism of Lie algebras.

**p-map.** Only `(h t)^[p]` carries a `z`-term, and `tau` maps Cartan `t^1`
elements to Cartan `t^1` elements and root vectors to root vectors. Now

```text
Phi((ht)^[p]) = (pi h) t^p + (alpha'(h) + kappa tr(S_pi h)) z,
Phi(ht)^[p] = (pi h) t^p + alpha(pi h) z.
```

So `Phi` is restricted iff `alpha'(h) = alpha(pi h) - kappa tr(S_pi h)`. With
`pi hA = hB`, `pi hB = -(hA+hB)`, `tr(S_pi hA) = 0` and `tr(S_pi hB) = 1`,
this is

```text
alpha'_A = alpha_B,     alpha'_B = -alpha_A - alpha_B - kappa.
```

`Phi(rho(Y_i)) = rho(Y_(tau i))`, because `lambda` vanishes off the
diagonal. So `rho_alpha(tau_A T) = Phi(rho_(alpha')(T))` for every `T` in
`A`. For `T` in `I` at `(p,p,p)` this gives

> `zeta_(kappa,alpha)(tau_A T) = zeta_(kappa,alpha')(T)`.

In coordinates, if `zeta(T) = k kappa + v alpha_A + u alpha_B` has row
`(k,v,u)`, then

```text
tau_A T   : (k-u, -u, v-u),
tau_A^2 T : (k-v, u-v, -v).
```

`tau_A` carries the ca slice `(p,1,p)` to the ab slice `(p,p,1)`, and
`tau_A^2` carries it to the bc slice `(1,p,p)`.

**Check.** The ca row at `p = 5, 7, 11` is `(0,0,-1)`. Its rotations are
`(1,1,1)` and `(0,-1,0)`. These are `-S_ab` and `-S_bc`, the values computed
independently in the ab and bc slices (edge-jump claim; (P11)).

## (Red) Reduction of (E_p) to one scalar (proved from (S), (A), (T))

Let `T_sigma` in `I` be the lift of the Witt-carry syzygy (S). By (A) its row
is `(k, 0, 6)`, with `k = k(p)` its Kassel coordinate. Then:

- the rows of `T_sigma`, `tau_A T_sigma` and `tau_A^2 T_sigma` are
  `(k,0,6)`, `(k-6,-6,-6)` and `(k,6,0)`;
- for general `(k,v,u)` the three rows have determinant
  `(3k-u-v)(u^2-uv+v^2)`, so here it is `108 (k-2)`;
- `108 = 2^2 3^3` is a unit for `p >= 5`.

So the three rotated elements have independent values iff `k(p) != 2 mod p`.
That independence is what (R2) of the edge-jump claim uses: three elements
of `I` at `(p,p,p)`, one per edge slice, with independent `zeta`. When each
edge slice has a single `rho`-visible jump, as at `p = 5, 7, 11`, these are
the edge jumps and the condition is exactly `(E_p)`.

**Invariant form.** The fixed point of `alpha -> alpha'` at `kappa = 1` is
`alpha_A = alpha_B = -1/3`. On `N_(1,-1/3,-1/3)`, `Phi` is an automorphism,
and `zeta(T_sigma) = k - 6/3 = k - 2`. So

> `(E_p)` holds iff the Witt-carry syzygy of the ca edge does not vanish on
> the rotation-invariant Kassel extension `N_(1,-1/3,-1/3)`.

## (K) The Kassel coordinate k(p) (exact for p = 5, 7, 11, 13)

The Kassel coordinate is

```text
k(p) = 2 pi1(p-3) - 9 pi1(p-2) + 2 pi2(p-3) + 3 pi2(p-2),
```

with every pairing evaluated at `alpha = 0`. The rows for `p <= 11` come
from the full tables (`pairs.out`, §3). The row for `p = 13` comes from
`SEEDFORM` (§4):

| p | `pi1(p-2)` | `pi1(p-3)` | `pi2(p-2)` | `pi2(p-3)` | `k(p)` |
|---|---|---|---|---|---|
| 5  | 0 | 4 | 3 | 4 | 0 |
| 7  | 2 | 1 | 2 | 5 | 0 |
| 11 | 5 | 8 | 5 | 7 | 0 |
| 13 | 6 | 4 | 2 | 7 | 0 |

So `k(p) = 0` and `k(p) - 2 = -2 != 0` at these primes.

**Independent recomputation.** The mode `SEEDFORM=1` of `fo_dual.cpp`
recomputes the four pairings and `zeta(sigma)` from the closed-form seeds
(S0) alone. It builds `E23^(p-2) E13^2 m0` and `-E23^(p-2) (E21 t)^2 m0`
directly in `M`, with no relator expansion. It agrees at `p = 5, 7, 11` for
all three values of `alpha` (§4): `ZETA_SIGMA` is `0, 0, 6` for
`alpha = (0,0), (1,0), (0,1)`.

At `p = 13` the full `PAIRTAB` run does not fit. `SEEDFORM` fits, with its
memo capped (`LMMCAP=400000`). It takes 812 s and uses about `2.7 * 10^6`
monomials of `M`, peak RSS about 1.1 GB. It gives `k(13) = 0`. At
`alpha = (0,1)` it gives `ZETA_SIGMA = 6` (549 s), which matches (A). The seeds used there are the
`SEEDGEN` t-parts at `p = 13` (§5), so this row is exact.

The reflection `a <-> c` fixes the ca slice and gives no constraint on `k`.

The individual pairings have no evident closed form. For example,
`pi2(p-3)` is `3/2` at `p = 5, 7, 11` but not at `p = 13`. Only the
combination `k(p)` is visibly regular.

## Status

- **Proved outright:** the syzygy space and the uniqueness of the carry
  syzygy `sigma` (S); the rotation lemma (T); the determinant reduction
  (Red).
- **Proved from the seed formula (S0):** the restricted part `6 alpha_B`
  (A). (S0) itself is numeric for `p = 5, 7, 11, 13`.
- **Argued, not formalised:** the lift of `sigma` to `I` (S). It is checked
  against the program's jump at `p = 5, 7` (`SEEDSUM OK`, §1).
- **Exact computation:** (P11) and (K), with `p = 13` in (K).

**Consequence.** `(E_p)`, and with it the `n=1` case of Open 2 of
`kms-hc1-a2-pro-p-completion-is-iwahori-criterion` given Open 1, holds for
`p = 5, 7, 11`. It holds for `p = 13` given the lift. For every `p >= 17`
it is equivalent to `k(p) != 2 mod p`, given (S0) and the lift.

**Open.** A symbolic evaluation of the Kassel part `k(p)` of the four
pairings.

- The derivation count of (A) handles the `alpha`-terms, where every factor
  becomes a Cartan element at `t^1`.
- The `kappa`-terms come from the straightening in `M`: a factor at `t^i`
  meets one at `t^(p-i)`, or a factor at `t^(p-1)` meets `c` or `e`.
- The numerics suggest `k(p) = 0` (`p = 5, 7, 11, 13`).

A route that avoids the count is to show directly that the ca syzygy does
not vanish on the rotation-invariant extension `N_(1,-1/3,-1/3)`. On that
extension `Phi` is an automorphism of order 3, so the three edge slices can
be treated at once.
