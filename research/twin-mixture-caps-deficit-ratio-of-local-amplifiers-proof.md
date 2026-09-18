---
rg: 2
id: twin-mixture-caps-deficit-ratio-of-local-amplifiers-proof
kind: route
title: Feed the amplifier a satisfiable twin mixed with a NO instance, then compare with the NO instance alone; for tensor powers count the all-twin block
target: twin-mixture-caps-deficit-ratio-of-local-amplifiers
requires: []
artifacts:
  - experiments/ugc-amplifier-mixture-2026-09-17/check_twin_mixture.py
---

Notation is as in the target. Only definitions are used. The corollary reads
the numbers `((1-eps)/2, eps)` from `unique-games-hard-at-completeness-one-half`
and uses nothing else from it.

**Lemma 1 (values of unions and products).**

1. `val(A + B) = (||A|| val A + ||B|| val B)/(||A|| + ||B||)`.
2. `val(nX) = val(X)`.
3. For games `G_1, ..., G_t`, `prod_i val(G_i) <= val(G_1 x ... x G_t) <= min_i val(G_i)`.

*Proof.* (1) A vertex lies in exactly one part and every edge stays inside
one part. So a labeling is a pair of independent labelings, and the satisfied
mass adds. (2) follows from (1).

(3) The lower bound: label every coordinate by an optimal labeling of its
factor. An edge is satisfied if every coordinate is, and the weights
multiply. For the upper bound, fix `i` and a labeling `(f, g)` of the
product, with `f` on the left and `g` on the right. For every choice `z` of
edges of the other factors, with probability proportional to its weight, the
left prover labels `u` by the `i`-th coordinate of `f(u, left ends of z)`,
and the right prover likewise with `g`. The two provers use the same `z`,
fixed in advance. Averaged over `z`, the satisfied mass fraction in `G_i` is
at least the fraction of product edges satisfied in coordinate `i`, which is
at least `val` of the product labeling. Some `z` does at least as well as the
average. QED.

**Lemma 2 (twin mixtures).** Let `S` be a satisfiable twin of `H`, and
`a, b >= 0` integers with `a + b >= 1`. Put `lambda = a/(a+b)`. Then
`val(aS + bH) = lambda + (1 - lambda) val(H)` and `val((a+b)H) = val(H)`.

*Proof.* `||S|| = ||H||` because the weighted graphs are equal. Apply Lemma 1
with `val S = 1`. QED.

**Proof of Theorem A.** `lambda = (c - s_H)/(1 - s_H)` is a rational in
`(0, 1)`, since `s_H < c < 1`. Write it as `a/(a+b)` with positive integers
`a, b`. Let `S` be the twin of `H`, and put `M = aS + bH` and `N = (a+b)H`.
Both lie in `C`. By Lemma 2, `val M = c` and `val N = s_H <= s`. So `M` is a
YES instance and `N` a NO instance, and

```text
val Red(M) >= c',        val Red(N) <= s'.
```

Take `P_S`, `P_H` and `E` from twin-splitting, and put `m = ||P_H|| = ||P_S||`,
`e = val E` and `v = val P_H`. Both outputs have mass `(a+b) m + ||E||`. Put
`rho = ||E||/((a+b) m + ||E||)`. By Lemma 1 and `val P_S <= 1`,

```text
val Red(M)  <=  rho e + (1 - rho)(lambda + (1 - lambda) v),
val Red(N)   =  rho e + (1 - rho) v.
```

Put `X = rho (1 - e) >= 0` and `Y = (1 - rho)(1 - v) >= 0`. Then

```text
1 - c'  >=  1 - val Red(M)  >=  X + (1 - lambda) Y,
1 - s'  <=  1 - val Red(N)   =  X + Y.
```

Now `1 - s' > 0`, so `X + Y > 0`. Also `1 - lambda > 0`, so
`X + (1 - lambda) Y > 0`, and `c' < 1`. The ratio is

```text
R(c', s')  <=  (X + Y)/(X + (1 - lambda) Y)  <=  1/(1 - lambda).
```

The last step holds because `(X + Y)(1 - lambda) <= X + (1 - lambda) Y`, which
is `-lambda X <= 0`. Finally
`1 - lambda = (1 - c)/(1 - s_H)`.

If `E` is empty, then `rho = 0`, and
`c' <= val Red(M) <= lambda + (1 - lambda) s'`, because `v = val Red(N) <= s'`.
QED.

**Consequences.** `(1 - s_H)/(1 - c) <= 1/(1 - c)`. For the second bullet,
pad a NO instance `H_0` of value `v_0 <= s` by `P_nu` with
`nu = (s - v_0)/(1 - v_0)`. That is a rational in `[0, 1)`, and by item 1 of
`ug-hardness-deficit-ratio-padding-line` the result has value exactly `s`.

*Bounded distortion, `E` empty.* Put `m_S = ||P_S|| <= D m_H`. By Lemma 1,

```text
val Red(M) <= (a m_S + b m_H v)/(a m_S + b m_H),   and   v <= s'.
```

So `1 - c' >= b m_H (1 - s')/(a m_S + b m_H)`. Hence

```text
R' <= (a m_S + b m_H)/(b m_H) <= 1 + D a/b = 1 + D (R_H - 1),
```

because `a/b = lambda/(1 - lambda) = R_H - 1`.

**GL is in TS.** Since `graph(S) = graph(H)`, we get
`graph(aS + bH) = graph((a+b)H)`, and so both inputs get the same parameter
`theta`. By (L1),

```text
Phi(aS + bH) = a Phi(S) + b Phi(H),     Phi((a+b)H) = (a+b) Phi(H).
```

By (L2), `||Phi(S)|| = ||Phi(H)||`. Take `E` empty.

**Closure.**

*Post-padding.* Let `mu` be a function of `graph(x)`, so that `M` and `N`
get the same `mu`. `P_mu(Y)` is `(1 - mu)`-rescaled `Y` plus one identity
edge of mass `mu ||Y|| / (1 - mu)`. The two outputs `Red(M)` and `Red(N)`
have equal mass, so the identity edge gets the same weight in both. Rescale
`P_S`, `P_H` and `E` by `1 - mu`, and add the identity edge to `E`.

*Pre-padding.* `P_nu(aS + bH)` is `a S' + b H' + I`. Here `S'` and `H'` are
`S` and `H` rescaled by `1 - nu`, and `I` is an identity edge whose weight
depends only on `graph(x)`. `P_nu((a+b)H)` is `(a+b) H' + I` with the same
`I`. A GL map `Phi` applied next gets the same `theta` on both inputs,
because their graphs agree. By (L1) it outputs
`a Phi(S') + b Phi(H') + Phi(I)` and `(a+b) Phi(H') + Phi(I)`, so
`E = Phi(I)`.

*Adding a component depending only on `graph(x)`.* It is the same component
for `M` and `N`, so it goes into `E`.

*Post-composing with mass-proportional GL maps.* Let `Phi_2` be GL with
`||Phi_2(A)|| = kappa ||A||`, and parameter a function of `graph(x)`. Then

```text
Phi_2(a P_S + b P_H + E) = a Phi_2(P_S) + b Phi_2(P_H) + Phi_2(E),
```

and the same for `N`, with `||Phi_2(P_S)|| = kappa m = ||Phi_2(P_H)||`.

**Members.**

* *Edge gadgets of mass `kappa w_e`.* An edge gadget lies inside the
  component of its edge, which gives (L1). Its total mass is
  `kappa ||A||`, which gives (L2).
* *Code compositions.* Vertex tables are indexed by the vertex, and each test
  reads the two tables of one edge. This gives (L1). The test measure of an
  edge has mass `w_e`, which gives (L2).
* *Walk powering.* A walk never leaves its component, which gives (L1). The
  walk measure (stationary start, weighted steps) has mass determined by the
  weighted graph, which gives (L2).
* *2-path, star games and lifts.* These are the same argument. For the 2-path
  game, the pair `(e, f)` at a left vertex `u` gets weight
  `w_e w_f / W_u`, so the total mass is `||A||`. The artifact checks this case
  exactly.

**Proof of Theorem B.** Let `S_0` be the twin of `H_0`. Put

```text
lambda_Y = (c - v_0)/(1 - v_0),    lambda_N = (s - v_0)/(1 - v_0),
```

so `0 <= lambda_N < lambda_Y < 1`. Write `lambda_Y = a/(a+b)` and
`lambda_N = a'/(a'+b')`. Let `Y = a S_0 + b H_0` and `N = a' S_0 + b' H_0`.
By Lemma 2, `val Y = c` and `val N = s`.

The t-th tensor power of a disjoint union is the disjoint union, over words
`w` in the parts, of the products `G_(w_1) x ... x G_(w_t)`. The question to
each prover determines the word. The mass of the word `w` is
`prod ||G_(w_i)||`. All parts have mass `||H_0||`, so the words with only
`S_0` letters carry mass fraction `lambda^t`.

* Those blocks have value `1`.
* Every other block has an `H_0` factor, so by Lemma 1(3) its value is at most
  `v_0`.

By Lemma 1(1),

```text
c'  <=  val(Y^(x t))  <=  lambda_Y^t + (1 - lambda_Y^t) v_0,
s'  >=  val(N^(x t))  >=  lambda_N^t.
```

So `1 - c' >= (1 - lambda_Y^t)(1 - v_0) > 0` and `1 - s' <= 1 - lambda_N^t`.

For `0 <= x < y < 1`,

```text
(1 - x^t)/(1 - x) = 1 + x + ... + x^(t-1)  <=  1 + y + ... + y^(t-1) = (1 - y^t)/(1 - y).
```

Hence

```text
R' <= (1 - lambda_N^t)/((1 - lambda_Y^t)(1 - v_0))
   <= (1 - lambda_N)/((1 - lambda_Y)(1 - v_0))
    = R(c, s)/(1 - v_0),
```

using `1 - lambda_N = (1 - s)/(1 - v_0)` and
`1 - lambda_Y = (1 - c)/(1 - v_0)`.

With `v_0 = s` we get `lambda_N = 0` and the bound `1/(1 - c)`. A final
padding `P_mu` moves the thresholds along the padding orbit, which keeps `R`.
QED.

**Proof of the Corollary.**

* The class `C` of linear games over `F_2^l` is closed under `+` and under
  twins (put `b_e := 0`).
* The source point has NO instances. By `unique-games-hard-at-completeness-one-half`
  they exist, for example of value `<= eps`.
* Theorem A, first consequence, and Theorem B with `H_0` a NO instance give
  `R' <= 1/(1 - c)`. At `c = (1-eps)/2` this is `2/(1 + eps) < 2`.
* By item 2 of `ug-hardness-deficit-ratio-padding-line`, `R' < 2` means
  `s' > 2c' - 1`.

QED.
