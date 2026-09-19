---
rg: 2
id: dkkms-seed-law-is-uniform-in-regime-and-far-in-window-proof
kind: route
title: Count valid extensions to see that the edge law is the seed law times a constant kernel, condition the covering lemma twice for uniformity, and test the event that a block projection lies in a coordinate axis for the window lower bound
target: dkkms-seed-law-is-uniform-in-regime-and-far-in-window
requires:
  - dkkms-near-perfect-labellings-are-outer-honest
  - dkkms-certified-parameters-lie-in-the-selector-kill-regime
artifacts:
  - experiments/dkkms-covering-window-2026-09-17/seed_law_at_dkkms_beta.py
---

The notation is that of the target. Write `n := 3k`. Every space is over
`F_2`. The number of `j`-subspaces of an `N`-space is written `[N, j]`.

## Premises used

* **(Cov)** DKKMS Lemma 4.9, as quoted in (Q6) of
  `dkkms-near-perfect-labellings-are-outer-honest-proof`: if
  `2^(l-1) beta <= 1/8` and `l - 1 > 1`, then `TV(P0, Q) <= beta sqrt(k) 2^(l+3) = d`.
* **(N)** Corollary N of `dkkms-near-perfect-labellings-are-outer-honest`,
  together with its proof step (2), `delta_U = rej_Q <= 2 eta_U + SD(P, Q)`.
* **(C)** Theorem C of `dkkms-certified-parameters-lie-in-the-selector-kill-regime`:
  every certified point with `l >= 5` is in (R) and (A).
* **(Fin)** A law on a finite set that is invariant under a group acting
  transitively on the set is uniform.

## Step 1: the edge law is the seed law times a constant kernel

Let `A := { R in Gr(X_U, l-1) : R meet H_U = 0 }`. Call `L` a *valid
extension* of `R` if `L > R`, `dim L = l` and `L meet H_U = 0`.

**Claim 1.** If `R` is in `A`, then `R` has exactly
`N := (2^n - 2^(k+l-1)) / 2^(l-1)` valid extensions. If `R` is not in `A`, it
has none.

*Proof.* If `R` is not in `A`, then every `L > R` meets `H_U`. Now let `R` be
in `A`, so `dim(R + H_U) = k + l - 1`. For `x` not in `R`, the space
`L = R + <x>` meets `H_U` iff some `r + x` with `r` in `R` lies in `H_U`, that
is iff `x` lies in `R + H_U`. So the valid `x` are the
`2^n - 2^(k+l-1)` vectors outside `R + H_U`. Each valid `L` contains exactly
`2^l - 2^(l-1) = 2^(l-1)` vectors outside `R`, and all of them are valid `x`
for the same `L`. `square`

The DKKMS edge law given `U` draws `R ~ P0`, then `L` uniform among the valid
extensions of `R`, and conditions on at least one existing. By Claim 1 that
event is `A`, so

```text
P(R, L)   = P0(R | A) * 1[L valid ext of R] / N,
nu0(R, L) = Q(R | A)  * 1[L valid ext of R] / N.                     (1.1)
```

Hence `P` and `nu0` have seed marginals `P0(. | A)` and `Q(. | A)`, and they
share the kernel from seed to A-space. So

```text
TV(P, nu0) = TV(P0(. | A), Q(. | A)).                                (1.2)
```

`nu0` is uniform on valid pairs. Given a valid `L`, every hyperplane `R` of
`L` satisfies `R meet H_U <= L meet H_U = 0`, so `(R, L)` is a valid pair. Hence
`nu0(. | L) = u_L`, the uniform law on the `2^l - 1` hyperplanes of `L`.
`P(. | L) = w(. | L)` is also supported on those hyperplanes.

**Claim 2.** Suppose `k >= l - 1`. Then `P0(A^c) <= 2^(l-1-k)` and
`Q(A^c) <= 2^(l-1-2k)`.

*Proof.* Condition on a smoothing `V` with `j` smoothed blocks. Then
`dim X_V = n - 2j >= k >= l - 1`, and `R` is uniform in `Gr(X_V, l-1)`.

- A nonzero vector of `H_U` is a sum of block all-ones vectors over a nonempty
  set `S` of blocks. It lies in `X_V` iff no block of `S` is smoothed, because
  a smoothed block contributes only one coordinate to `X_V`. So
  `|H_U meet X_V| = 2^(k-j)`.
- For a fixed nonzero `h` in `X_V`,
  `Pr[h in R] = (2^(l-1) - 1)/(2^(n-2j) - 1) <= 2^(l-1-n+2j)`.

The union bound gives
`Pr[R meet H_U != 0 | V] <= 2^(k-j) 2^(l-1-3k+2j) = 2^(l-1-2k+j) <= 2^(l-1-k)`.
The same computation with `j = 0` over all `2^k` vectors of `H_U` gives
`Q(A^c) <= 2^(l-1-2k)`. `square`

## Step 2: two conditioning lemmas

**Lemma 1.** Let `mu, nu` be laws on a finite set and `A` an event with
`mu(A), nu(A) > 0`. Then `TV(mu(. | A), nu(. | A)) <= 2 TV(mu, nu) / mu(A)`.

*Proof.* For every `S`,

```text
|mu(S meet A)/mu(A) - nu(S meet A)/nu(A)|
   <= |mu(S meet A) - nu(S meet A)| / mu(A)
      + (nu(S meet A)/nu(A)) * |nu(A) - mu(A)| / mu(A)
   <= TV(mu, nu)/mu(A) + TV(mu, nu)/mu(A).
```

Take the supremum over `S`. `square`

**Lemma 2.** Let `P, nu` be laws on pairs `(R, L)`, with `L`-marginals `P_L`
and `nu_L`. Where `nu_L(L) = 0`, let `nu(. | L)` be any law. Then

```text
E_(L ~ P_L) TV(P(. | L), nu(. | L))  <=  TV(P, nu) + TV(P_L, nu_L)  <=  2 TV(P, nu).
```

*Proof.* The left side equals
`(1/2) sum_(R,L) |P(R,L) - P_L(L) nu(R|L)|`. The triangle inequality through
`nu(R, L) = nu_L(L) nu(R|L)` bounds it by
`(1/2) sum |P(R,L) - nu(R,L)| + (1/2) sum_L |nu_L(L) - P_L(L)| sum_R nu(R|L)`.
That is `TV(P, nu) + TV(P_L, nu_L)`. Marginalising does not increase total
variation. `square`

## Step 3: Theorem U

Assume `l >= 3`, `2^(l-1) beta <= 1/8` and `2^(l-1-k) <= 1/3`. The last
condition gives `k >= l + 1`, so Claim 2 applies and `P0(A) >= 2/3`.

1. By (Cov), `TV(P0, Q) <= d`.
2. By (1.2) and Lemma 1, `TV(P, nu0) <= 2d / P0(A) <= 3d`.
3. By Lemma 2 with `nu = nu0` and Step 1 (`nu0(. | L) = u_L`),
   `E_(L ~ P) TV(w(. | L), u_L) <= 6d`.
4. For every `R`, `w(R|L) - u_L(R) <= TV(w(. | L), u_L)`. So
   `max_R w(R|L) <= 1/(2^l - 1) + TV(w(. | L), u_L)`. Take expectations.

Under (R), `d <= SD* <= 10^(-5)`. (R) also implies `2^(l-1) beta <= 1/8` and
`2^(l-k) <= 1/200`, by the remark after the regime in
`near-perfect-selectors-on-rigid-dkkms-instances-put-np-in-rp`, and the latter
gives `2^(l-1-k) <= 1/3`. So the bounds become `6 * 10^(-5)` and
`1/(2^l - 1) + 6 * 10^(-5) <= 1/7 + 6 * 10^(-5)`. `square`

## Step 4: Theorem W

Let `E` be the set of `(l-1)`-spaces `R` for which some block `i` and some
coordinate `t` of that block satisfy `proj_i(R) <= <e_(i,t)>`. Equivalently,
`R` lies in the codimension-2 subspace `W_(i,t)` cut out by the other two
coordinates of block `i`.

* **`P0(E) >= 1 - (1 - beta)^k`.** If block `i` is smoothed and keeps variable
  `t`, then `proj_i(X_V) = <e_(i,t)>`. Since `R <= X_V`, this forces
  `R in E`. At least one block is smoothed with probability `1 - (1 - beta)^k`.
* **`Q(E) <= 3k 4^(1-l)`.** For a fixed codimension-2 subspace `W`, a uniform
  `(l-1)`-space lies in `W` with probability
  `prod_(i=0)^(l-2) (2^(n-2) - 2^i)/(2^n - 2^i) <= 4^(-(l-1))`. Each factor is
  `<= 1/4` because `4(2^(n-2) - 2^i) <= 2^n - 2^i`. There are `3k` subspaces
  `W_(i,t)`.

So `TV(P0, Q) >= P0(E) - Q(E) >= 1 - (1 - beta)^k - 3k 4^(1-l)`. This holds
whenever `P0` is defined, that is, whenever `k >= l - 1`.

**Seed marginals.** For any law `mu` and event `A`, `TV(mu(. | A), mu) = mu(A^c)`.
By the triangle inequality and Claim 2,

```text
TV(P0(.|A), Q(.|A)) >= TV(P0, Q) - P0(A^c) - Q(A^c)
                    >= 1 - (1-beta)^k - 3k 4^(1-l) - 2^(l-1-k) - 2^(l-1-2k),
```

which is at least the stated bound with `2^(l-2k)`. By (1.2) the same bound
holds for `TV(P, nu0)`, since edge laws are at least as far apart as their
seed marginals.

**Transitive laws.** By (Fin), a law of `(l-1)`-spaces invariant under a group
acting transitively on `Gr(X_U, l-1)` is `Q`. So the bound applies to it, and to
every `GL(X_U)`-invariant ideal test.

**The rate.** `(1 - beta)^k <= exp(-beta k)`.
- Natural reading: `beta k = ln ln k`, so this is `1/ln k`.
- Base-2 reading: `beta k = log2 log2 k`, so this is
  `(log2 k)^(-1/ln 2) <= (log2 k)^(-1) <= 1/ln k` once `log2 k >= 1`.

**The window.** For `k <= k_T(l) = 4^(l-1)/12` we have `3k 4^(1-l) <= 1/4`,
which gives `TV(P0, Q) >= 3/4 - 1/ln k`. Also
`2^(l-1-k) + 2^(l-2k) <= 2^(1+l-k)`. `square`

## Step 5: window arithmetic

At `q = 1`, admissibility is `2^(l-1-2k) <= 1/16` together with
`exp(-k/e^l) <= p0^2/4 = 2^(-2l)/(4 * 192^2)`. The second condition is
`k >= e^l (2 l ln 2 + ln(4 * 192^2)) = k_A(l)`, with
`ln(4 * 192^2) = 11.9013`. The first condition holds for every `k >= l`.

Put `f(l) := k_T(l)/k_A(l) = 4^(l-1) / (12 e^l (c l + c_0))`, with
`c = 2 ln 2` and `c_0 = 11.9013`. Then

```text
f(l+1)/f(l) = (4/e) (c l + c_0)/(c l + c + c_0) >= (4/e)(c + c_0)/(2c + c_0) = 1.332   (l >= 1).
```

So `f` is increasing. Direct evaluation gives `f(19) = 0.839` and
`f(20) = 1.191`, so `k_T(l) >= k_A(l)` exactly for `l >= 20`. The interval
`[k_A, k_T]` then has length `>= 0.19 k_A > 1` and contains integers.
Asymptotically `f(l) = Theta((4/e)^l / l)`.

**Window points lie outside (R).** For `k <= k_T(l)` we have
`sqrt(k) <= 2^(l-1)/sqrt(12)`. So

```text
d = beta k 2^(l+3) / sqrt(k) >= 16 sqrt(12) beta k >= 55 beta k.
```

For `k >= k_A(20) > 2^34`, `beta k >= min(ln ln k, log2 log2 k) > 3`. So
`SD* >= d > 165`, far above `10^(-5)`.

## Step 6: Corollary T

1. **`T1`.** At an admissible point in (R), Corollary N gives what `T` asks,
   with `eta_1 = 10^(-5)`, `zeta_1 = 1/128`, outer value `>= 15/16` and dirt
   `<= 1/64`, on every 3LIN input. (R) supplies the side conditions of
   Theorem R, as recalled in Step 3. By (C), every certified point with
   `l >= 5` is in (R) and (A), so it is an admissible point of `T1`.
2. **`T <=> T2`.** Admissible points split into those in (R) and those
   outside it. `T` restricted to either part is implied by `T`. Conversely,
   given `T2` with constants `(eta', zeta', l')`, the constants
   `(min(eta', 10^(-5)), max(zeta', 1/128), max(l', 3))` give `T`. Here
   "value `>= 1 - eta_1`" is monotone in `eta_1` and agreement outside mass
   `zeta_1` is monotone in `zeta_1`. By (C), no certified point with
   `l >= 5` lies outside (R).
3. **The window.** By Step 5, at `q = 1` every `k` in `[k_A(l), k_T(l)]` is
   admissible and outside (R), so it is a point of `T2`. The transfer (2) of the
   outer-honest route compares two laws.
   - One is `P`, on `(L', L_1, L_2)`. Its seed marginal is
     `P0(L') w(L')/Z`. By Claim 1, `w` is a positive constant on `A` and `0`
     off `A`, so this marginal is `P0(. | A)`.
   - The other is `Q`, with seed marginal uniform.

   Hence

   ```text
   SD(P, Q) >= TV(P0(.|A), Q) >= TV(P0, Q) - P0(A^c) >= 3/4 - 1/ln k - 2^(l-1-k),
   ```

   by Step 4 and Claim 2. The same holds if `Q` is replaced by any test whose
   seed law is invariant under a transitive group, because that seed law is
   uniform by (Fin). For `l >= 20` we have `k >= k_A(20) > 2^34`, so
   `1/ln k < 0.043` and `2^(l-1-k)` is negligible. So `SD(P, Q) > 0.7 >= 1/2`,
   and (2) cannot give `delta_U < 1/2`. The later steps of that route need
   `delta_U` below a small absolute constant: `20 delta_U + SD*` must be small
   in the A-side bound. `square`

## Step 7: Corollary P4

Assume the hypotheses of Theorem U with `6d <= 10^(-4)`. Suppose that on a set
of A-mass `>= 1 - delta` the conditional seed law puts weight `>= 1 - xi` on
one hyperplane (the generating one or any other). Then

```text
(1 - delta)(1 - xi) <= E_L max_R w(R|L) <= 1/(2^l - 1) + 6d <= 1/7 + 10^(-4)
```

by Theorem U with `l >= 3`. Since `1 - delta - xi <= (1 - delta)(1 - xi)`, the
value `1 - delta - delta' - xi` that Proposition 4 guarantees is
`<= 0.14296 < 0.1431`.

Every point of (R) satisfies the hypotheses with `6d <= 6 * 10^(-5)`. By (C),
so does every certified point with `l >= 5`. The dominant-hyperplane labelling
of the smoothing node satisfies an edge only when its seed is the dominant
hyperplane, so its value is `E_L max_R w(R|L)`, which is bounded by the same
quantity. `square`

## What the artifact checks

- Claims 1 and 2 are used implicitly by the fast sampler. It is validated
  against explicit rejection sampling of the DKKMS process, in Section 3a of
  the script.
- Theorem U is checked in Section 3: `E_L TV(w(.|L), u_L) <= 2 TV(P0, Q)` at
  every tested point, and `E max w` approaches `1/(2^l - 1)`.
- Theorem W and Step 5 are checked in Section 4.
- The closed form of `P0/Q` used for the Monte Carlo total variation is checked
  against the exact dynamic program in Section 1.
