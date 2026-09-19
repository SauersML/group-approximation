---
rg: 2
id: value-free-star-list-references-put-np-in-rp-proof
kind: route
title: Charge references for broken outer constraints instead of demanding value, read outer consistency off the good stars themselves, pigeonhole on good-star mass, and get the outer value from Cauchy-Schwarz through the seed-to-B marginal
target: value-free-star-list-references-put-np-in-rp
requires:
  - list-star-coherent-selector-witnesses-put-np-in-rp
  - efficient-branch-selectors-list-decode-honest-outer-labels
  - dkkms-2to1-instances-satisfy-selector-decoding-hypotheses
artifacts:
  - experiments/ugc-value-free-star-2026-09-17/check_value_free_star.py
---

Notation is that of the target. The list computed in step 4 of the decoder is
written `Gamma`, as in the Theorem CL proof.

## Step 1: the star inequality with consistency charges

Fix a YES input and condition on the event, of probability `>= theta`, that
`o = S(x)` carries `W` and `Lambda` as in the hypothesis. Fix `o`, `W`,
`Lambda`. Put `H := (sigma, tau)`, the projection of `W`, and `h_q` the seed
label of `W` at `q`. Let `T` be the set of constraints `W` satisfies in `U_o`.

Step 1 of the Theorem CL proof gives `T subset Sat(H)`, `mu(T) >= 1/2 + gamma`,
and, for every star `(w, a)` and every `j`,

```text
beta^j_(w,a)  >=  Pr[T | w, a] - Pr[X_j | w, a] - 1/2 ,      X_j := X(H, lambda^j).
```

That step uses no property of `lambda^j` beyond being a labelling of `A`. Since
`X_j subset X^C_j := X^C(H, lambda^j)`, the same bound holds with `X^C_j` in
place of `X_j`. Let `j(w,a)` minimise `Pr[X^C_j | w, a]`, and put
`beta*_(w,a) := beta^(j(w,a))_(w,a)`. Then

```text
E_nu beta*  >=  mu(T) - D^C_L(H, Lambda) - 1/2  >=  gamma' ,
```

and, since `beta* <= 1/2`, `P := Pr_nu[beta* >= gamma'/2] >= gamma'`. Call a
star **good** if `beta*_(w,a) >= gamma'/2`.

## Step 2: a good star certifies outer consistency of its reference

Let `(w, a)` be good and `j := j(w,a)`. Then
`Pr[T | w,a] - Pr[X^C_j | w,a] >= 1/2 + gamma'/2 > 0`, so some constraint `e`
with `(w_e, a_e) = (w, a)` lies in `T \ X^C_j`. As `T subset Sat(H)`, that `e`
lies in `Sat(H) \ X^C_j`, so `pi_(a_e b_e)(lambda^j_(a_e)) = lambda^j_(b_e)`.
By (Bw), `b_e = b(w)`. Hence

```text
C^j_(a, b(w))  :  pi_(a b(w))(lambda^j_a) = lambda^j_(b(w))      holds at every good star (w,a), j = j(w,a).
```

## Step 3: decoding and pigeonhole on good-star mass

Step 2 of the Theorem CL proof applies unchanged at a good star: it used only
(E_tau) at `(w,a)` and the advantage `beta* >= gamma'/2` of the fixed linear
form `lambda^j_a`. So, when the decoder draws this `w` and guesses `s = h_w`
(probability `>= 2^(-l)`), it outputs `lambda^j_a` with probability
`>= gamma'^2/4`.

For `a in A` and each `j`, put `q^j_a := Pr[hat lambda_a = lambda^j_a]` and

```text
g^j_a := Pr_(w ~ nu(.|a)) [ (w,a) good and j(w,a) = j ].
```

The decoder draws `w ~ nu(.|a)`, so `q^j_a >= kappa g^j_a` with
`kappa = 2^(-l) gamma'^2/4`. Also `sum_j g^j_a = Pr_(w|a)[good]`, whose
`nu_A`-mean is `P >= gamma'`. Hence some `j*` has
`E_(nu_A) g^(j*) >= gamma'/L`, and by (M) `E_(rho_A) g^(j*) >= gamma'/(K L)`.
Fix this `j*` and drop it from the notation: `lambda := lambda^(j*)`,
`q_a := q^(j*)_a`, `g_a := g^(j*)_a`. The index is used only in the analysis.

**Consistency mass.** Let `c_a := Pr_(b ~ rho(.|a))[C_ab]`, where
`C_ab := {pi_ab(lambda_a) = lambda_b}`. By Step 2, `g_a` is at most the
probability, over `w ~ nu(.|a)`, that `C_(a, b(w))` holds. The law of `b(w)`
under `w ~ nu(.|a)` is the law of `b_e` given `a_e = a` under `mu`, by (Bw).
So by (M_B),

```text
g_a  <=  Pr_(mu)[ C_(a, b_e) | a_e = a ]  <=  K1 c_a .
```

Therefore

```text
E_((a,b) ~ rho) [ q_a 1_(C_ab) ]  =  E_(rho_A) [ q_a c_a ]  >=  (kappa / K1) E_(rho_A) [ g_a^2 ]
                                  >=  (kappa / K1) (E_(rho_A) g)^2  >=  kappa gamma'^2 / (K1 K^2 L^2) .
```

(Check A verifies both inequalities of this display and the Step 4 bound
exactly on 300 random toy outer games, with arbitrary labellings and
adversarial wrong decoder outputs.)

## Step 4: outer value with no value hypothesis

The B-rule draws `a' ~ rho(.|b)` and sets `hat lambda_b := pi_(a'b)(hat lambda_(a'))`.
Draw `(a, b) ~ rho` and let `a'` be the B-rule's draw at `b`, so given `b` the
vertices `a` and `a'` are independent `rho(.|b)` draws. The decoded edge
`(a,b)` is satisfied when all four events hold:

* `X := {hat lambda_a = lambda_a}` and `C := C_ab`;
* `Y := {hat lambda_(a') = lambda_(a')}` and `D := C_(a'b)`.

Then `pi_ab(hat lambda_a) = pi_ab(lambda_a) = lambda_b = pi_(a'b)(lambda_(a')) = hat lambda_b`.
`C` and `D` are deterministic given `(a, a', b)`, since `lambda` is fixed. The
decoder's coins at distinct `A`-vertices are independent. So for `a != a'`,
`Pr[X, Y, C, D | a, a', b] = (q_a 1_(C_ab)) (q_(a') 1_(C_(a'b)))`. For `a = a'`
the edge is satisfied surely, which is `>= (q_a 1_(C_ab))^2`. Hence, by Jensen,

```text
E val_Phi(hat lambda)  >=  E_b [ ( E_(a ~ rho(.|b)) q_a 1_(C_ab) )^2 ]
                       >=  ( E_rho [ q_a 1_(C_ab) ] )^2
                       >=  ( kappa gamma'^2 / (K1 K^2 L^2) )^2
                       =   p^2 gamma'^2 / (K1^2 K^4 L^4)  =  c0^C_L ,
```

using `kappa gamma' = p`. No `eps` term appears. The events `C` and `D` are not
bounded through the value of `lambda`, which may be tiny. They are carried by
the good-star mass through Step 3.

Values lie in `[0,1]`, so `Pr[val_Phi(hat lambda) >= c0^C_L/2] >= c0^C_L/2`.
On NO inputs every outer labelling has value `<= s < c0^C_L/2` by (S^C_L), so
the decoder never accepts. On YES inputs it accepts with probability
`>= theta c0^C_L/2`. Repeating `O(1/(theta c0^C_L))` times gives
`Lang in RP`. This proves Theorem CLV. `square`

## Step 5: Corollary IMP

Let every `lambda^j` have `val_Phi >= 1 - eps`. Write
`Inc_j := {e : pi_(a_e b_e)(lambda^j_(a_e)) != lambda^j_(b_e)}`. At each star,
`min_j mu(X^C_j | w,a) <= mu(X_(j0) | w,a) + sum_j mu(Inc_j | w,a)`, where `j0`
minimises `mu(X_j | w,a)`. Averaging over `nu` gives
`D^C_L <= D_L + sum_j mu(Inc_j)`. By (M) and (M_B), the `mu`-law of
`(a_e, b_e)` is `mu_A(a) mu(b|a) <= K rho_A(a) K1 rho(b|a) = K K1 rho(a,b)`. So
`mu(Inc_j) <= K K1 (1 - val_Phi(lambda^j)) <= K K1 eps`. Summing over `j`
gives `D^C_L <= D_L + L K K1 eps`. `square`

## Step 6: Corollary DK^C

**(Bw).** In `dkkms-2to1-instances-satisfy-selector-decoding-hypotheses` the
seed of a copy is `w_e = (V, L')`, its A-vertex is `U`, and the copy is built
from the outer edge `(U, V)`. So `b(V, L') = V`.

**(M_B).** Step 3 of `dkkms-selector-membership-proof` (the route of that node)
writes the law of `(U, V, L', L)` before validity conditioning as
`P(U) P(V|U) |Gr(X_V, l-1)|^(-1) N^(-1)`. Its Step 4 gives the validity
probability given `(U, V)`:

```text
Pr[valid | U, V]  =  Pr_(L')[ L' cap H_U = {0} | V ] * |S|/N ,
|S|/N  =  (2^(3k) - 2^(l-1+k)) / (2^(3k) - 2^(l-1)) .
```

Here `L'` is uniform in `Gr(X_V, l-1)`, and `L' cap H_U = L' cap (X_V cap H_U)`,
where `X_V cap H_U` has dimension `t` inside the `(2t+k)`-dimensional space
`X_V`. So the law of `V` given `U` under `mu` is
`P(V|U) Pr[valid|U,V] / Pr[valid|U]`, while `rho(V|U) = P(V|U)`. Hence

```text
mu(V | U) / rho(V | U)  =  Pr[valid | U,V] / Pr[valid | U]  <=  1 / min_V Pr[valid | U,V] ,
```

because `Pr[valid|U]` is a `P(.|U)`-average of `Pr[valid|U,V] <= 1`.

A uniform `L'` has `2^(l-1) - 1` nonzero vectors. By `GL(X_V)`-invariance each
is uniform on `X_V \ {0}`, so each lies in the `t`-space with probability
`(2^t - 1)/(2^(2t+k) - 1) <= 2^(-t-k)`. The union bound gives
`Pr[L' cap H_U != {0}] <= 2^(l-1-t-k) <= 2^(l-1-k)`. Also
`|S|/N >= 1 - 2^(l-1-2k)`. So

```text
Pr[valid | U,V]  >=  1 - 2^(l-1-k) - 2^(l-1-2k)  >=  1 - 2^(l-k) ,
```

and `K1 <= 1/(1 - 2^(l-k))`, which is `<= 2` for `k >= l+1`.

Check B computes the exact ratio from Gaussian binomials. The formula is
verified by brute force for dimensions `<= 5`. Over `l = 2..4`, `k = l+1..15`
and four values of `beta`, the ratio is below the bound everywhere, e.g.
`K1 = 1.0196` at `l = 2, k = 3, beta = 0.2`.

**The rest.** Items 3 and 4 and the Corollary of the same node give
(E_tau) with `tau = 2^(l-1-2k)`, (M) with `K = 1`, and
`eps_k = exp(-k/exp(ql))` as the NO-instance outer value (Lemma 5.4 of DKKMS).
With `K = 1` and `K1 <= 2`, `c0^C_L/2 >= p^2 gamma'^2 / (8 L^4)`. Suppose
`L < (p gamma'/3)^(1/2) exp(k/(4 exp(ql)))`. Then
`L^4 < (p^2 gamma'^2/9) exp(k/exp(ql))`, so
`eps_k < p^2 gamma'^2/(9 L^4) < c0^C_L/2`, which is (S^C_L). Take `k` large
enough that also `2^(l-1-2k) <= gamma'/4` and `k >= l+1`. `square`

## Step 7: Corollary HON

Take `lambda = lambda^y`. Step 5 of `dkkms-selector-membership-proof` shows
that if `U` is clean for `y`, then `hon(y)_(p_e) = y|_L` and
`ev_e(hon(y)_(p_e)) = <y|_U, x_e> = <lambda^y_U, x_e>`. The outer projection
`pi_UV` is restriction on labels that satisfy the equations of `U`. When `U` is
clean, `y|_U` satisfies them, so `pi_UV(lambda^y_U) = y|_V = lambda^y_V`.

So a constraint `e` can lie in `X^C(H, lambda^y)` only if `U` is dirty for `y`
or `sigma_(p_e) != hon(y)_(p_e)`. The `U`-marginal of `mu` is `rho_A` (`K = 1`,
Step 4 there), so the dirty mass is exactly `eps_out(y)`. With `L = 1` the star
average is just `mu(X^C)`. `square`

## Remark: the local-fix labelling (Check C)

Let `y` violate a `delta` fraction of the equations. Define `lambda'` as
follows: on `U`, flip the first variable of each violated equation; on `V`,
apply the same flip on each whole violated equation. The edge `(U,V)` is
inconsistent only if some violated equation of `U` was not kept whole
(probability `beta` each) and the kept variable is the flipped one
(probability `1/3`). With disjoint equations this gives
`val_Phi(lambda') = (1 - beta delta/3)^k`.

At `beta = log log k / k` and `k delta = O(1)` the loss is
`O(log log k / k)`. Check C confirms the formula by Monte Carlo at
`k = 16..1024`. The claim's Remark draws the consequence: on DKKMS, Corollary
HON is also reachable from Theorem CL.
