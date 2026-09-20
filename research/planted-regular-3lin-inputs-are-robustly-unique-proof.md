---
rg: 2
id: planted-regular-3lin-inputs-are-robustly-unique-proof
kind: route
title: Slot measures are within 1 +- 9k^2/n of uniform on D-regular instances; a Doob martingale over the D permutations (transposition coupling, Lipschitz 2) plus Azuma and a union bound gives every set of density >= 0.06/k an odd-equation fraction >= 0.09/k; a near-optimal a differs from x* on a set whose odd equations are violated by a or by x*, so a + x* is sparse and RU holds with C = 0
target: planted-regular-3lin-inputs-are-robustly-unique
requires: []
artifacts:
  - experiments/ugc-planted-ru-2026-09-17/check_planted_ru.py
  - experiments/ugc-planted-ru-2026-09-17/check_planted_ru.out
---

The notation is that of the target. Write `viol_unif(a)` for the fraction of
the `m` equations that `a` violates. For `z in F_2^n`, write `z(e)` for the
sum of `z` over the three variables of `e`, and put
`odd(z) := #{e : z(e) = 1}` and `viol^hom_unif(z) := odd(z)/m`,
`viol^hom_omega(z) := omega({e : z(e) = 1})`.

## Imported tools (verbatim citations)

**Azuma's inequality.** N. Alon and J. Spencer, *The Probabilistic Method*,
Theorem 7.2.1: "Let `0 = X_0, ..., X_m` be a martingale with
`|X_(i+1) - X_i| <= 1` for all `0 <= i < m`. Let `lambda > 0` be arbitrary.
Then `Pr[X_m > lambda sqrt(m)] < e^(-lambda^2/2)`."

Applied to `(X_i - X_0)/c` and to `-(X_i - X_0)/c`, this gives, for a
martingale with differences at most `c` in absolute value and `t > 0`,

```text
Pr[ X_m <= X_0 - t ]  <  exp( - t^2 / (2 c^2 m) ) .                    (Az)
```

**Binomial tails, from (Az).** If `S` is a sum of `m` independent
`{0,1}`-valued variables, then `X_i := sum_(j<=i) (Y_j - E Y_j)` is a
martingale with differences at most `1`. Applying (Az) to `X` and to `-X`
gives, for `s > 0`,

```text
Pr[ S >= E S + s m ]  <  exp(-s^2 m / 2),     Pr[ S <= E S - s m ]  <  exp(-s^2 m / 2) .   (Bin)
```

No other probabilistic tool is used.

## Step 1: the slot measures are almost uniform

Let the instance be `D`-regular with `m = Dn/3` equations on three distinct
variables each, and let `U` be a uniform ordered `k`-tuple of pairwise
variable-disjoint equation slots (*legitimate* tuples, indexed by positions
in `Eq`, so repeated triples count separately). Assume `n > 9k`.

The uniform law on legitimate ordered tuples is invariant under permuting
the slots, so every slot has the same marginal and
`omega(e) = Pr[slot 1 = e] = N_e / N`. Here `N_e` is the number of legitimate
tuples with first slot `e`, and `N = sum_f N_f`.

An equation shares a variable with at most `3D` equations, itself included,
because each of its three variables lies in exactly `D` equations. Choose
slots `2, ..., k` in order. When slot `j + 1` is chosen, `j` equations are
already fixed and block at most `3Dj` positions. So

```text
prod_(j=1)^(k-1) (m - 3Dj)   <=   N_e   <=   m^(k-1) .
```

Since `prod (1 - 3Dj/m) >= 1 - 3D k^2/(2m) >= 1 - 9k^2/n =: 1 - delta`,
we get `N_e / m^(k-1) in [1 - delta, 1]` for every `e`. Hence

```text
(1 - delta)/m  <=  omega(e)  <=  1/((1 - delta) m) .                     (W)
```

For a variable `v`, each slot equal to `e` contributes one variable slot
equal to `v` exactly when `v in e`. So
`nu({v}) = (1/(3k)) sum_(e ni v) E[# slots equal e] = (1/3) sum_(e ni v) omega(e)`.
There are exactly `D` such `e`, and `D/(3m) = 1/n`, so

```text
(1 - delta)/n  <=  nu({v})  <=  1/((1 - delta) n) .                     (N)
```

Consequently, for every set `S` of equations and every set `T` of variables,

```text
omega(S) in [ (1-delta)|S|/m, |S|/((1-delta)m) ],
nu(T)    in [ (1-delta)|T|/n, |T|/((1-delta)n) ] .
```

The artifact (Part D) checks (W) and (N) by exact enumeration.

## Step 2: one triple

Let `Z ⊆ [n]` with `|Z| = w`, and let `T` be a uniform 3-subset of `[n]`.
Put `q_n(w) := Pr[|T ∩ Z| odd]` and

```text
q(p) := 3p(1-p)^2 + p^3 = 3p - 6p^2 + 4p^3 = (1 - (1-2p)^3)/2 .
```

`q(p)` is the probability that `|T' ∩ Z|` is odd when `T'` is three
independent uniform draws from `[n]`, with `p = w/n`. Conditioned on the three
draws being distinct, `T'` is a uniform 3-subset. Therefore
`|q_n(w) - q(w/n)| <= Pr[not distinct] <= 3/n`, because the total-variation
distance between a law and its conditioning on an event `A` is at most
`Pr[not A]`.

`q'(p) = 3 - 12p + 12p^2 = 3(1 - 2p)^2 >= 0`, so `q` is non-decreasing on
`[0, 1]`. For `p0 := 0.06/k` and `k >= 3` (so `2 p0 <= 0.04`),

```text
q(p0)  >=  3 p0 (1 - 2 p0)  >=  0.18/k * 0.96  =  0.1728/k .
```

Each triple of each factor is a uniform 3-subset, since the image of a fixed
3-set of positions under a uniform permutation is uniform. So for
`|Z| >= p0 n` and `n >= 300k`,

```text
E[odd(1_Z)]  =  (Dn/3) q_n(|Z|)  >=  (Dn/3) (q(p0) - 3/n)  >=  (Dn/3) (0.1628/k) .
```

## Step 3: threshold expansion (lemma E)

**Lemma E.** Let `k >= 3`, `n >= 300k`, `D >= 2 * 10^4 k^2`, `p0 = 0.06/k`
and `theta = 0.09/k`. With probability `>= 1 - exp(-0.77 n)` over the `D`
permutations, every `Z ⊆ [n]` with `|Z| >= p0 n` has
`viol^hom_unif(1_Z) >= theta`.

*Proof.* Fix `Z`, and let `f(pi_1, ..., pi_D) := odd(1_Z)`. Reveal the values
`pi_1(1), ..., pi_1(n), pi_2(1), ..., pi_D(n)` one at a time, and let
`X_0, ..., X_(nD)` be the Doob martingale `X_i := E[f | first i values]`.
So `X_0 = E f` and `X_(nD) = f`.

*Differences.* Consider step `i`, which reveals `pi_j(s)`, with the earlier
values fixed. For two candidate values `u != u'` of `pi_j(s)`, the map
`pi_j -> tau_(u u') ∘ pi_j`, where `tau_(u u')` swaps the values `u` and `u'`,
is a bijection between completions with `pi_j(s) = u` and completions with
`pi_j(s) = u'`. It preserves the earlier revealed values, because `u` and
`u'` are both unrevealed. It preserves the uniform law of the other
permutations. It changes at most the two triples of factor `j` that contain
`u` and `u'`. Each triple changes `f` by at most `1`, so `f` changes by at
most `2`. Hence the conditional expectations given `pi_j(s) = u` and given
`pi_j(s) = u'` differ by at most `2`. `X_i` is one of these values, and `X_(i-1)` is
their average over the unrevealed `u`. So `|X_i - X_(i-1)| <= 2`.

*Tail.* By Step 2, `E f >= (Dn/3)(0.1628/k)`, while `theta m = (Dn/3)(0.09/k)`.
Put `t := (Dn/3)(0.0728/k) <= E f - theta m`. By (Az) with `c = 2` and
`nD` steps,

```text
Pr[ f < theta m ]  <=  Pr[ f <= E f - t ]  <  exp( -t^2/(8 n D) )
                   =   exp( -(0.0728)^2 D n / (72 k^2) )  <=  exp( -1.47 n ),
```

using `D >= 2 * 10^4 k^2`. A union bound over at most `2^n` sets `Z` gives
failure probability `< 2^n e^(-1.47 n) <= e^(-0.77 n)`. QED.

## Step 4: the planted YES side

Let the instance be planted, from `M(n, D, eps/2)`. Given the permutations,
the number `S` of equations violated by `x*` is `Bin(m, eps/2)`. By (Bin)
with `s = eps/4`,

```text
Pr[ S > (3 eps/4) m ]  <  exp( -eps^2 m / 32 )  =  exp( -eps^2 D n / 96 )  <=  exp( -0.2 n ),
```

using `D >= 20/eps^2`. On the complement, `viol_unif(x*) <= 3eps/4`. By (W),
`viol_omega(x*) <= (3eps/4)/(1 - delta) <= eps`, since `delta <= 1/4`. So `x*`
satisfies a `1 - eps` fraction of `Eq` and has `val_omega(x*) >= 1 - eps`.
Regularity holds by construction, and every equation has three distinct
variables. This is a regular Gap3Lin YES input of completeness `1 - eps`
(in both the uniform and the `omega` sense).

## Step 5: the random NO side

Let `b` be uniform. For a fixed `a`, the number of equations `a` satisfies is
`Bin(m, 1/2)`. By (Bin) with `s = eps/2`, it exceeds `(1/2 + eps/2) m` with
probability `< exp(-eps^2 m/8) = exp(-eps^2 D n/24) <= exp(-(5/6) n)`, using
`D >= 20/eps^2`. A union bound over the `2^n` assignments gives failure
probability `< exp(-(5/6 - ln 2) n) <= exp(-0.14 n)`. On the complement,
`val_unif(a) <= 1/2 + eps/2` for every `a`. By (W),

```text
val_omega(a)  <=  (1/2 + eps/2)/(1 - delta)  <=  1/2 + eps ,
```

because `delta <= eps/4` (from `n >= 36 k^2/eps`) and `delta <= 1/100` give
`(1/2 + eps/2)(1 + 2 delta) <= 1/2 + eps/2 + delta(1 + eps) <= 1/2 + eps`.
So the random instance is a NO input of `Gap3Lin(1 - eps, 1/2 + eps)` in both
senses. If NO is read with the uniform value alone, the bound
`1/2 + eps/2` is already enough.

## Step 6: robust uniqueness with C = 0

Work on the intersection of the events of Lemma E and Step 4, which has
probability `>= 1 - exp(-0.77 n) - exp(-0.2 n) >= 1 - 3 exp(-0.2 n)`. Let
`n >= max(900 k^2, 36 k^2/eps)`, so `n >= 300k`, `n > 9k` and
`delta = 9k^2/n <= min(1/100, eps/4)`.

Let `a` have `val_omega(a) >= 1 - kappa` with `kappa = eps + gamma'/(4k)`, and
put `z := a + x*`. If `z(e) = 1`, then `a(e) != x*(e)`, so exactly one of `a`
and `x*` satisfies `e`. Hence `{e : z(e) = 1}` is contained in the union of the
equations violated by `a` and by `x*`, and

```text
viol^hom_omega(z)  <=  viol_omega(a) + viol_omega(x*)  <=  kappa + (3eps/4)/(1 - delta) .
```

With `k eps <= gamma/4 <= 0.02625` and `gamma' < gamma <= 0.105`, we have
`kappa < 0.0525/k` and `(3eps/4)/(1 - delta) <= 0.0199/k`. By (W),

```text
viol^hom_unif(z)  <=  viol^hom_omega(z)/(1 - delta)  <  0.0724/(0.99 k)  <  0.0732/k  <  theta .
```

By Lemma E, `|supp z| < p0 n`. By (N),

```text
dist_nu(a, x*)  =  nu(supp z)  <=  |supp z| / ((1 - delta) n)  <  0.06/(0.99 k)  <  0.061/k  =  rho* .
```

So (RU_(kappa, rho*, 0)) holds with this `x*` and `C = {0}`. This proves
item 1 of Theorem PR, and Step 5 proves item 2. Part A of the artifact
re-derives every numerical inequality of Steps 2-6 in exact rationals at the
worst admissible parameters, for `k = 3..200`. For larger `k` all the
`k`-dependence is through the factor `1/k` shown above.

Finally, `rho* = 0.061/k < 0.89/(12 k) < (1 - beta0)/(12k)` for every
`beta0 < 0.11`, and `r0 = 0 <= l + 1`. So the planted instance lies in RU-YES
for every radius `rho in [rho*, (1 - beta0)/(12k))` and every `r0 >= 0`. The
membership conditions of RU-YES in `gap3lin-hard-with-robustly-unique-yes-solutions`
are regular Gap3Lin, completeness `1 - eps`, and (RU_(eps + gamma'/(4k), rho, r0)).
They are exactly what Steps 4 and 6 give.

## Step 7: Corollary PR

Let `E_Y` be the event that a planted draw is in RU-YES, and `E_N` the
event that a random draw is in NO. By Theorem PR, `Pr[not E_Y] <= 3 e^(-0.2 n)`
and `Pr[not E_N] <= e^(-0.14 n)`.

* **Two-sided.** Let `A^r` be the majority of `r` independent runs. On any
  RU-YES input it accepts with probability `>= 1 - e^(-r/72)`, and on any NO
  input with probability `<= e^(-r/72)`, by (Bin) with `s = 1/6`. So
  `Pr_planted[A^r accepts] - Pr_random[A^r accepts] >= 1 - 2e^(-r/72) - Pr[not E_Y] - Pr[not E_N]`.
* **One-sided.** Let `A'` accept if any of `T = ceil(n / theta(n))` runs
  accepts. On RU-YES it accepts with probability
  `>= 1 - (1 - theta)^T >= 1 - e^(-n)`, and on NO it never accepts. The
  advantage is `>= 1 - e^(-n) - Pr[not E_Y] - Pr[not E_N]`.

Both distinguishers run in polynomial time. Only large `n` matters, so
finitely many exceptional sizes are harmless.

## The hypothesis the corollary contradicts (context, not used logically)

The distinguishing problem in Corollary PR is planted-versus-random noisy
3XOR with `m = Dn/3 = Theta(n)` equations, constant noise `eps/2`, and a
regular random 3-uniform hypergraph as the constraint structure. It is
believed hard for polynomial-time algorithms. This belief underlies
Alekhnovich's public-key scheme (FOCS 2003) and the random-3XOR refutation
threshold `m ~ n^(1.5)`. Supporting evidence includes the Grigoriev (2001) and
Schoenebeck (2008) sum-of-squares lower bounds for random 3XOR with
`m = O(n)`. Those results are stated for the Erdős–Rényi-style model. The
regular (union of triangle factors) model used here is a standard variant,
but its hardness is part of the hypothesis and is not transferred here. The
nodes built on Corollary PR state this hypothesis explicitly as an
assumption. Nothing in Theorem PR depends on it.

## Remark S (other soundness values)

Step 5 used only `D >= 20/eps^2` and `delta <= eps/4`. Replace `eps` by
`sigma := min(eps, s* - 1/2)` there. With `D >= 20/sigma^2` and
`n >= 36 k^2/sigma`, the same computation gives `val_unif(a) <= 1/2 + sigma/2 <= s*`
and `val_omega(a) <= 1/2 + sigma` for every `a`, with failure probability
`<= exp(-0.14 n)`. Steps 1-4 and 6 need only `D >= 20/eps^2`, which is implied
because `sigma <= eps`.
