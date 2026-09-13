---
rg: 2
id: coinvariant-tarski-lemma-minimal-nowhere-scattered-proof
kind: route
title: Take a defect above x from minimality, divide every piece by N with remainders of size at most 1/(N+2) of the piece, and move all pieces at once
target: coinvariant-tarski-lemma-minimal-nowhere-scattered
requires: []
---

Notation as in the claim.

**Congruence.**  By (R), `~` is an equivalence relation compatible with
addition, and `[y] = 0` forces `y = 0`, so `Sigma` is conical.  This is the
first paragraph of `coinvariant-tarski-lemma-simple-dimension-groups-proof`
(Rainone, Lemma 4.7), which uses only (R).

**Step 1: `Sigma` is simple.**  Fix a nonzero `x in G^+`.  Let `L` be the set of
`y in G^+` with `y <= sum_(j<=n) alpha_(t_j)(x)` for some `t_1, ..., t_n`.
`L` contains `x`, is closed under addition, is hereditary in `G^+`, and is
`Gamma`-invariant.  Put `H = L - L`.  If `0 <= h = a - b` with `a, b in L`, then
`h <= a`, so `h in L`.  Hence `H cap G^+ = L`, and `H` is a nonzero
`Gamma`-invariant order ideal (Rainone, Theorem 3.7, `(4) => (3)`).  By
minimality `H = G`.  So every `y in G^+` satisfies
`y <= sum_j alpha_(t_j)(x)`, and `[y] <= n[x]`.

**Step 2: a defect above `x`.**  Write `N[x] = N[x] + [e]` with `e in G^+`
nonzero, that is, `Nx + e ~ Nx`.

* Since `alpha_s(e) ~ e`, we get `Nx + alpha_s(e) ~ Nx + e ~ Nx`.
* If `Nx + e_1 ~ Nx` and `Nx + e_2 ~ Nx`, then `Nx + e_1 + e_2 ~ Nx + e_2 ~ Nx`.

By Step 1 applied to `e`, choose `s_1, ..., s_K` with `x <= E := sum_k alpha_(s_k)(e)`.
Then `E != 0` by conicality, and `Nx + E ~ Nx`.  So there are
`c_1, ..., c_m in G^+` and `t_1, ..., t_m in Gamma` with

```text
sum_i c_i = N x,        sum_i alpha_(t_i)(c_i) = N x + E.
```

**Step 3: divide.**  Put `M = N + 2`.  By (ND) choose `d_i in G^+` with
`N d_i <= c_i` and `M f_i <= c_i`, where `f_i := c_i - N d_i in G^+`.

**Step 4: one move.**  Let `y = sum_i d_i`.  Since `N(x - y) = sum_i f_i >= 0`,
(P) gives `r := x - y in G^+`.  Moving the pieces `d_i` by `t_i` and `r` by the
identity gives

```text
x = sum_i d_i + r   ~   x' := sum_i alpha_(t_i)(d_i) + r.
```

Now

```text
N (x' - x) = sum_i [ alpha_(t_i)(N d_i) - N d_i ]
           = sum_i [ alpha_(t_i)(c_i) - c_i ] - sum_i [ alpha_(t_i)(f_i) - f_i ]
           = h + sum_i f_i,          h := E - sum_i alpha_(t_i)(f_i).
```

Since `M alpha_(t_i)(f_i) = alpha_(t_i)(M f_i) <= alpha_(t_i)(c_i)` and `x <= E`,

```text
M h  >=  M E - sum_i alpha_(t_i)(c_i)  =  M E - N x - E  >=  (M - N - 1) E  =  E.
```

So `M h >= E >= 0`, and (P) gives `h in G^+`.  Also `h != 0`: otherwise
`0 >= E >= 0` and conicality gives `E = 0`.  Hence
`N(x' - x) = h + sum_i f_i` is positive and nonzero.  By (P),
`e' := x' - x in G^+ \ {0}`, and `[x] = [x'] = [x] + [e']` is infinite.

The estimate does not depend on the number `m` of pieces.  This is why no
state, density or order unit is needed.  In the simple case
(`coinvariant-tarski-lemma-simple-dimension-groups-proof`) the division error
had to be chosen after `m`.

**Step 5: proper infiniteness.**  From `[x] = [x] + [e']` we get
`[x] = [x] + k[e']` for every `k`.  Step 1 gives `k` and `zeta` with
`k[e'] = [x] + zeta`.  Then `[x] = [x] + k[e'] = 2[x] + zeta`, so `2[x] <= [x]`.

**Consequences.**  Suppose `(k+1) theta <= k theta` with `theta != 0`.  Then
`k >= 1` by conicality, and

```text
k theta = (k+1) theta + zeta = k theta + (theta + zeta),     theta + zeta != 0.
```

So `k theta` is infinite, and `theta` is properly infinite by the lemma with
`N = k`.  If `Sigma` has no nontrivial state, Tarski's theorem (Rainone,
Theorem 4.11) gives such a `k` for every nonzero `theta`, so `Sigma` is purely
infinite.  Conversely, if `2 theta <= theta` then `nu(theta)` is `0` or
`infinity` for every state `nu`.

**Model-test verifications.**

* *Simple noncyclic dimension groups.*  For `c != 0` the group has order unit
  `c`, and by Effros--Handelman--Shen its image is dense in `Aff(S(G, c))`,
  with `g > 0` iff `g^ > 0` on `S`.  Put `delta = 1/(4NM)` and choose `d` with
  `d^` in `(1/N - 3 delta, 1/N - delta)`.  Then `d^ > 0` and
  `1 - N d^ in (N delta, 3/(4M))`, so `d`, `c - N d` and `c - M(c - N d)` are
  strictly positive.
* *`C(X, Z[1/2])`.*  The order is pointwise.  For each of the finitely many
  values `v > 0` of `c`, pick a dyadic `w` in `[v(1 - 1/M)/N, v/N]`, and let `d`
  take the value `w` wherever `c` takes the value `v`.
* *Minimality binds.*  In `Z[1/2] direct_sum Z[1/2]` with `alpha(a, b) = (2a, b)`:
  * nonzero first coordinates are all equidecomposable, and the second
    coordinate is additive and invariant;
  * so `Sigma = {0, infinity} x Z[1/2]^+`;
  * `(infinity, 1)` is infinite but not properly infinite;
  * (R), (P) and (ND) hold, but `0 direct_sum Z[1/2]` is an invariant ideal.
