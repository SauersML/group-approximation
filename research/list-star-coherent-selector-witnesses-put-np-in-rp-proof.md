---
rg: 2
id: list-star-coherent-selector-witnesses-put-np-in-rp-proof
kind: route
title: Pick the best list member separately at every seed star, run the seed-guessing decoder unchanged, pay 1/L in the pigeonhole, and bound the star-list mass of mixtures by fibre collisions and of image-determined mixtures by a rank count
target: list-star-coherent-selector-witnesses-put-np-in-rp
requires:
  - efficient-branch-selectors-list-decode-honest-outer-labels
  - near-perfect-selectors-die-on-every-rigid-doubled-lec
  - constant-bias-selectors-need-seed-dishonest-witnesses
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
  - dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures
artifacts:
  - experiments/ugc-list-star-2026-09-17/check_list_star.py
---

Notation is that of the target. To avoid a clash with the list `Lambda` of the
hypothesis, the set computed in step 4 of the decoder is written `Gamma`.

## Step 1: Theorem CL, the star inequality

Fix a YES input and condition on the event, of probability `>= theta`, that
`o = S(x)` carries `W` and `Lambda` as in the hypothesis. Fix `o`, `W` and
`Lambda`. Everything below is over the decoder's coins only. Put
`H := (sigma, tau)`, the projection of `W`, and `h_q := (tau_q, b_q)`.

Let `T` be the set of constraints that `W` satisfies in `U_o`. Then `T` lies in
`Sat(H)` and `mu(T) >= 1/2 + gamma`. For `e` in `T`, the bit-free branch
identity of `near-perfect-selectors-die-on-every-rigid-doubled-lec` gives
`G_e(h_(q_e)) = ev_e(sigma_(p_e))`.

Write `X_j := X(H, lambda^j)`. If `e` is in `T \ X_j`, then
`ev_e(sigma_(p_e)) = <lambda^j_(a_e), x_e>`, since `T` lies in `Sat(H)`. So
`e` is predicted correctly by `lambda^j`.

For a star `(w, a)` in the support of `nu` and each `j`, put

```text
beta^j_(w,a) := Pr[ G_e(h_w) = <lambda^j_a, x_e> | w_e = w, a_e = a ] - 1/2.
```

Then, for every `j`,

```text
beta^j_(w,a)  >=  Pr[T | w, a] - Pr[X_j | w, a] - 1/2 .
```

Let `j(w,a)` minimise `Pr[X_j | w, a]`, and put
`beta*_(w,a) := beta^(j(w,a))_(w,a)`. Averaging over `nu`,

```text
E_nu beta*  >=  mu(T) - D_L(H, Lambda) - 1/2
            >=  (1/2 + gamma) - (gamma - gamma') - 1/2  =  gamma' .
```

Since `beta* <= 1/2`, Step 1 of the efficient-branch proof gives
`P := Pr_nu[beta* >= gamma'/2] >= gamma'`.

(Check A0 tests the star inequality on 400 random stars. Check A1 tests
`P >= gamma'`.)

## Step 2: a good star lists its own reference

The bit function `G_e` is computable in polynomial time from `o`, as in Step 3
of the constant-bias proof. Fix a star `(w, a)` with `beta*_(w,a) >= gamma'/2`,
and suppose the decoder drew `s = h_w`. This has probability `>= 2^(-l)`.

Put `j := j(w,a)`. Apply Step 2 of the efficient-branch proof with the linear
form `lambda^j_a` and advantage `beta*`. It gives
`hat F(lambda^j_a) >= 2 beta* - 2 tau >= gamma'/2`, since `tau <= gamma'/4`.
So `lambda^j_a` is in `Gamma`. By Parseval `|Gamma| <= 4/gamma'^2`, so the
decoder outputs `lambda^j_a` with probability `>= gamma'^2/4`.

That step used only (E_tau) at `(w, a)` and the advantage of one fixed linear
form. It does not depend on which form it is, so the form may change from star
to star.

## Step 3: union bound and pigeonhole

For each `A`-vertex `a` and each `j`, put `q^j_a := Pr[hat lambda_a = lambda^j_a]`
and `Q_a := Pr[hat lambda_a in {lambda^1_a, ..., lambda^L_a}]`. The decoder draws
`w` from `nu(. | a)`. Steps 1 and 2 give

```text
Q_a  >=  Pr_(w ~ nu(.|a)) [ beta*_(w,a) >= gamma'/2 ] * 2^(-l) * gamma'^2/4 ,
E_(nu_A) Q  >=  P 2^(-l) gamma'^2/4  >=  gamma'^3 2^(-l-2)  =  p .
```

By the union bound `Q_a <= sum_j q^j_a`, so `sum_j E_(nu_A) q^j >= p`. Hence
some `j*` has `E_(nu_A) q^(j*) >= p/L`. By (M),
`E_(rho_A) q^(j*) >= p/(KL)`.

The index `j*` depends on `o`, `W` and `Lambda`, which are fixed by the
conditioning. It is used only in the analysis. The decoder never computes it.

(Checks A2, A3 and A4.)

## Step 4: outer value

Step 4 of the efficient-branch proof uses one fixed outer labelling of value
`>= 1 - eps`, and the numbers `q_a = Pr[hat lambda_a = lambda_a]`. Apply it with
`lambda^(j*)` and `q^(j*)`. The decoder's coins at distinct outer vertices are
independent, so

```text
E val_Phi(hat lambda)  >=  (E_(rho_A) q^(j*))^2 - 2 eps  >=  p^2/(K^2 L^2) - 2 eps  =  c0_L .
```

Values lie in `[0, 1]`, so `Pr[val_Phi(hat lambda) >= c0_L/2] >= c0_L/2`.

The decoder accepts iff the decoded value is `>= c0_L/2`. On NO inputs every
outer labelling has value `<= s < c0_L/2` by (S_L), so it never accepts. On YES
inputs it accepts with probability `>= theta c0_L/2`. For fixed
`(gamma, gamma', l, K, L, eps)` with `c0_L > 0`, repeating `O(1/(theta c0_L))`
times gives `Lang in RP`. This proves Theorem CL. (Check A5.) `square`

The same argument holds when `L = L(|x|)` is computable in polynomial time and
`c0_L >= 1/poly`.

## Step 5: Corollary DK

Items 3 and 4 of `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses`
state (E) with `tau = 2^(l-1-2k)` and (M) with `K = 1` for
`(Phi_k, G_multi)`, with seed `(V, L')`. Its Corollary takes NO-instance outer
value `<= eps_k = exp(-k/exp(ql))` from Lemma 5.4 of DKKMS.

Take `k` so large that `2^(l-1-2k) <= gamma'/4`. Suppose `eps <= p^2/(8 L^2)`
and `eps_k < p^2/(8 L^2)`. Then

```text
c0_L/2  =  p^2/(2 L^2) - eps  >=  3 p^2/(8 L^2)  >  eps_k ,
```

so (S_L) holds. If `L < (p/3) exp(k/(2 exp(ql)))`, then
`L^2 < (p^2/9) exp(k/exp(ql))`. So `p^2/(8 L^2) > (9/8) eps_k > eps_k`.

For the good labellings, item 5 there gives `val_Phi(lambda^a) = 1 - eps_out(a)`,
with `eps_out(a) <= k eps_3 (1 + o(1))`. Choose `eps_3` after `k` with
`2 k eps_3 <= p^2/(8 L^2)`. So the parameters are chosen in the order `l`,
then `gamma` and `gamma'`, then `k`, then `eps_3`. The list size `L` may grow
with `k`, subject to the displayed bound. `square`

## Step 6: Corollary SF, and its converse

This is Lemma F of the constant-bias proof, with the reference chosen per seed.
At a star `(w, a)` with `w = q`, let `j(q)` be an index with
`tau_q = tau^(j(q))_q` if one exists, and `j(q) := 1` otherwise. Since `D_L`
takes a minimum at every star,

```text
D_L(H, Lambda)  <=  mu(Y),     Y := { e : e in X(H, lambda^(j(q_e))) } .
```

Take `e = (p, q)` in `Y` and put `j := j(q)`. There are three cases.
1. `tau_q` is not in `{ tau^i_q : i }`. Since `e` is in `Sat(H)`, the mass of
   these edges is at most `beta_L(H)`.
2. `tau_q = tau^j_q`, and `e` is a defect edge of `H^j`: either `e` is not in
   `Sat(H^j)`, or `ev_e(sigma^j_p) != <lambda^j_(a_e), x_e>`. Summed over `j`,
   the mass is at most `sum_j r_j`.
3. Otherwise `pi_e(sigma_p) = tau_q = tau^j_q = pi_e(sigma^j_p)` and
   `ev_e(sigma^j_p) = <lambda^j_(a_e), x_e> != ev_e(sigma_p)`. So
   `sigma_p != sigma^j_p` and the two collide under `pi_e`.

For fixed `p`, the third set lies in the union over `j` of the collision sets
of the fixed pairs `(sigma_p, sigma^j_p)`. Its conditional mass given
`p_e = p` is therefore at most `L c(p)`, and its mass is at most `L kappa`. That
proves the display of Corollary SF.

The seed form hands Theorem CL a star-list bound only when its right-hand side
is below `gamma`. That needs `L kappa < gamma`, which for Grassmann tests
(`kappa = 1/(2^l - 1)`) is `L < gamma (2^l - 1)`.

**Converse.** Let `Phi : F_2^X -> F_2^n` vanish on every `x_e`, and let `x` be
good. Each `x + c o Phi` (`c` a functional on `F_2^n`) satisfies exactly the
equations that `x` satisfies, so it is good with the same outer value. Its
honest encoding restricts, by Lemma 3(b) of
`dkkms-seed-rigidity-fails-on-homogeneous-kernel-mixtures-proof`, to
`(x + c o Phi)|_(L')` at every seed of a clean tuple.

Let `(V, L')` be a seed with `Phi` injective on `L'`, and let `tau_(V,L')` be
any label. Its difference from `x|_(L')` is a functional on `L'`. Since
`Phi(L')` has dimension `l - 1`, every functional on `Phi(L')` extends to some
`c`, and `c o Phi` agrees with that difference on `L'`. So the seed is covered.

It remains to bound the uncovered seeds. On a surjective `V`, `Phi` kills `H'`
and induces a surjection `Phi-bar : Q -> F_2^n`. By Lemma 2(a) there, the image
of `L'` in `Q` is uniform in `Gr(Q, l-1)`. Choose its basis vectors in turn.
The `(i+1)`-st must avoid a subspace of `Q` of dimension `d' - n + i`. So
`Pr[Phi not injective on L'] <= sum_(i<l-1) 2^(i-n) < 2^(l-1-n)`.

(Check D verifies the covering exactly for `n = l + 1`, `l = 2, 3, 4`.)

## Step 7: Proposition MIX

At the star `(w, a)` choose `j := i(w)`. Take `e = (p, q)` with `q = w` in
`X(H, lambda^j)`. Then `tau_q = tau^j_q`, so case 1 of Step 6 does not occur.

The case-2 mass, summed over `j`, is at most `sum_j r_j`. In case 3, if
`i(p) = j` then `sigma_p = sigma^j_p`, which contradicts `sigma_p != sigma^j_p`.
So `i(p) != j`, and `e` lies in the collision set of the pair
`(sigma^(i(p))_p, sigma^j_p)`.

For fixed `p` there are at most `L - 1` such pairs, one for each
`j != i(p)`. So the case-3 mass is at most `(L-1) kappa`. `square`

## Step 8: Proposition LS\*

**Well defined.** Each branch `x` or `y_d = x + <d, zeta(.)>` is a global
assignment satisfying every equation that `x` satisfies. The rule reads a
vertex `(U, L)` through `Phi(L)`, and `Phi(L) = Phi(L + H_U)` because `Phi`
kills `H_U`. So Lemma 3 of the Theorem M proof applies word for word, with
`phi` replaced by `Phi` and the pair `x, y` replaced by the branch family.
When every tuple is clean, the labelling `h` is constant on folding classes and
unfolds at every `(U, L)` to `beta(Phi(L))|_L`, where `beta(S)` is the branch
of `S`.

**The cross event.** Write every branch as `x + f o Phi` with a mask
`f in F_2^n`: `f = 0` for `x`, and `f = (0, d)` for `y_d`. Fix an edge copy
with seed `(V, L')`, target `U`, `L = L' + <x_e>` and direction `x_e`. Put
`f_B := f(Phi(L'))` and `f_A := f(Phi(L))`.

The edge is satisfied iff `(f_A + f_B) o Phi` vanishes on `L'`, since the two
labels share the `x` part. With the reference at the star chosen as the
B-branch `x + f_B o Phi`, which is in `Lambda`, the edge is ev-dishonest iff
`<f_A + f_B, Phi(x_e)> = 1`.

So, writing `u_1, ..., u_(l-1)` for the images of a basis of `L'` and
`u_l := Phi(x_e)`, the edge is in `X` for that reference iff

```text
g := f_A + f_B  is orthogonal to u_1, ..., u_(l-1)   and   <g, u_l> = 1,
```

where `f_B = f(W)`, `f_A = f(W~)`, `W = span(u_1..u_(l-1))` and `W~ = W + <u_l>`.
Hence `D_(2^s)(h, Lambda) <= Pr[that event]`.

**Item 1: image model.** Let the `u_i` be iid uniform in `F_2^n`. If the event
holds, then `g != 0`, so `f_A != f_B`. The case `f_A = (0, d)` and
`f_B = (0, d')` with both nonzero is impossible:
* `c(W)` is `<(0, d')>`;
* `c(W~)` contains `c(W)` and equals `<(0, d)>`;
* so `d = d'`.

So exactly one of `f_A, f_B` is a nonzero `(0, d)`, and `g = (0, d)`. In either
case `(0, d)` lies in `c(W~)`, which lies in `W~`. So `(0, d) = sum_i c_i u_i`
for some nonzero `c in F_2^l`.

Thus the event lies in the union, over `d != 0` in `F_2^s` and `c != 0` in
`F_2^l`, of

```text
E_(d,c):   sum_i c_i u_i = (0, d)   and   <(0, d), u_i> = 0  for i < l .
```

View `(u_1, ..., u_l)` as a vector of `F_2^n (x) F_2^l`, so that both lists of
constraints are affine in it.
* The first list is `n` independent equations, with functionals `f (x) c` for
  `f` ranging over a basis of the dual of `F_2^n`.
* The second list is `l - 1` independent equations, with functionals
  `(0, d) (x) e_i` for `i < l`.

A functional lies in both spans only if it is a rank-one tensor `f (x) c` that
equals some `(0, d) (x) a` with `a_l = 0`. That forces `f = (0, d)` and
`a = c`, so it spans at most one dimension. So the system has rank at least
`n + l - 2`. For iid uniform `u_i` the event then has probability at most
`2^-(n+l-2)`, or it is empty.

A union bound over the `(2^s - 1)(2^l - 1)` pairs gives, with `n = l + s`,

```text
chi  <=  (2^s - 1)(2^l - 1) 2^-(2l+s-2)  <  2^s 2^l 2^-(2l+s-2)  =  2^(2-l).
```

(Check C1 verifies the exact enumeration for `(l, s) = (3,1), (3,2), (3,3), (4,1)`.
Check C2 runs Monte Carlo for `s = l = 5, 6, 7`.)

**Item 2: transfer to DKKMS.** The event depends on the edge only through the
subspace `W = Phi(L')` and the vector `u_l = Phi(x_e)`. Condition on a clean
`V` on which `Phi` is surjective. Then `Phi` kills `H'` and induces a
surjection `Phi-bar : Q -> F_2^n`, with `Q = X_V/H'` of dimension `d' >= k`.

1. By Lemma 1 and Lemma 2(a) of the Theorem M proof, the image of `L'` in `Q`
   is uniform on `Gr(Q, l-1)`. A uniform ordered basis of it is a uniform
   linearly independent `(l-1)`-tuple in `Q`. That tuple is at total variation
   distance `<= Pr[iid uniform tuple is dependent] <= 2^(l-1-d')` from an iid
   uniform tuple.
2. The push-forward of an iid uniform tuple under the surjection `Phi-bar` is
   iid uniform in `F_2^n`.
3. Given `(V, L', U)`, the direction `x_e` is uniform on `X_U \ (L' + H_U)`, by
   Lemma 1 there and item 3 of the decoding-hypotheses node. That is at total
   variation distance `2^(l-1-2k)` from uniform on `X_U`, which is independent
   of `L'`. `Phi` is surjective on `X_U`, since `X_U` contains `X_V`. So
   uniform on `X_U` pushes forward to uniform on `F_2^n`.

Hence, given `V`, the pair `(W, u_l)` is within total variation
`2^(l-1-d') + 2^(l-1-2k) <= 2^(l-k)` of its image-model law. The conditional
probability of the cross event is at most `chi + 2^(l-k) < 2^(2-l) + 2^(l-k)`.
Averaging over `V`, and charging the non-surjective tuples in full, gives
item 2. `square`

## Step 9: Remark M1

Fix a clean `V` on which `Phi = (phi, z)` is surjective onto `F_2^(l+1)`, with
`b` and `c` as in Lemma 4 of the Theorem M proof.

**Item 1.** Take `e` in `Sat(h)`.
* If the A-branch of `e` is `y`, then `ev_e = y(x_e) = <lambda_y, x_e>`, so `e`
  is honest.
* If the A-branch is `x`, then `phi` is injective on `L`, hence on `L'`. So the
  B-branch is also `x`, the edge is satisfied, and it is ev-dishonest against
  `y` iff `z(x_e) = 1`.

So `D_V(h, lambda_y) = Pr[phi injective on L, z(x_e) = 1 | V]`. By Lemma 4(a),
`phi` is injective on `L'` with probability `b`.

Given such an `L'`, the direction `x_e = w` is uniform on `X_U \ (L' + H_U)`.
Count the `w` in `X_U` with `phi(w)` outside `phi(L')` and `z(w) = 1`:
* `(phi, z)` is surjective on `X_U`;
* `phi(L')` is a hyperplane of `F_2^l`;
* so the count is `2^(3k)/4 = 2^(3k-2)`;
* none of these lies in `L' + H_U`, which `phi` maps into `phi(L')`.

So the conditional probability is `2^(3k-2)/(2^(3k) - 2^(l-1+k)) = (1-c)/2`,
using `1 - c = 2^(3k-1)/(2^(3k) - 2^(l-1+k))`. Hence
`D_V(h, lambda_y) = b(1-c)/2` exactly.

Item 2 of Theorem M gives `val_V(h) >= 1 - bc`. So
`val_V - 1/2 - D_V >= 1/2 - b(1+c)/2`, and `c <= 1/2` gives `> 1/2 - 3b/4`.

For the sign: `b_l := Π_(j=2)^l (1 - 2^(-j))` decreases in `l`, with
`b_4 = 0.6152`. Also `b <= b_l / (1 - 2^(l-1-d'))`. So `b < 2/3`, and the
margin is positive, for `l >= 4` and `d' >= l + 3`.

The numbers quoted are check B3, at `k = d' = 4l`. The limit `D -> P_1/4`
follows from `b -> P_1` and `c -> 1/2`.

**Item 2.** Choose the reference at the star as the B-branch. The only cross
case is B-branch `x` with A-branch `y`. If it is satisfied, then
`y|_(L') = x|_(L')`, that is `z|_(L') = 0`. By Lemma 2(b) of the Theorem M
proof, with `w = z|_(X_V) != 0`, this has conditional probability
`<= 2^(1-l)`. `square`

(Check B1 verifies the exact law `Pr[z|_(L') = 0] <= 2^(1-l)`. Check B2
verifies the image model exactly for `l = 2, 3, 4`.)
