---
rg: 2
id: fpbs-layer-renewal-along-homomorphism-is-critical-l2-proof
kind: route
title: First band visit with BK, then symmetrized relative susceptibility of the co-amenable kernel for scalar coefficients, and a band decomposition of the two-point operator for operator coefficients
target: fpbs-layer-renewal-along-homomorphism-is-critical-l2
requires:
  - fpbs-co-amenable-subgroup-relative-threshold-is-pc
---

**Notation.** As in the target. `tau = tau_p`. The facts used about `tau`:
- **Invariance.** Left multiplication is a graph automorphism, so
  `tau(gx,gy) = tau(x,y)`. Also `tau(x,y) = tau(y,x)`, which gives
  `tau(o,x) = tau(x^(-1),o) = tau(o,x^(-1))`.
- **Harris–FKG.** `tau(x,z) >= tau(x,y) tau(y,z)`.

The height changes by at most `K` along an edge, since `h(xs) = h(x) + h(s)`.

## Step 1: renewal

Fix `i, j >= 1`, and let `(x,y)` lie in relative band `i+j`.

- **First band visit.** Suppose `x <-> y`, and let `gamma` be an open simple
  path from `x` to `y`. Let `z` be the first vertex of `gamma` with
  `h(z) - h(x) >= jK`. It exists because `h(y) - h(x) >= (i+j)K > jK`. Its
  predecessor has relative height `< jK`, and one step adds at most `K`. So
  `(x,z)` lies in relative band `j`.
- **Disjoint witnesses.** The segments `gamma[x,z]` and `gamma[z,y]` use
  disjoint edge sets. So `{x <-> y}` is contained in the union, over `z` in
  relative band `j` of `x`, of `{x <-> z} ∘ {z <-> y}`.
- **BK and a union bound.** These give

  ```text
  tau(x,y) <= sum_z R_j(x,z) tau(z,y).
  ```
- **Band of the second leg.** Here

  ```text
  h(y) - h(z) = (h(y)-h(x)) - (h(z)-h(x))  in  ((i-1)K, (i+1)K),
  ```

  so `(z,y)` lies in relative band `i-1` or `i`. Both are `>= 0`, since
  `i >= 1`.

This gives `R_(i+j) <= R_j (R_(i-1) + R_i)` entrywise. All kernels are
nonnegative, so operator norms are monotone under entrywise domination. This
gives the bound on `r_(i+j)`.

**Weighted scalar form.** Take `x = o`, `y in Lambda_(i+j)`, and write
`u = z^(-1) y`. Submultiplicativity gives `w(y) <= w(z) w(u)`. Also
`tau(z,y) = tau(o,u)`, and `h(u)` lies in band `i-1` or `i`. Summing over
`y`,

```text
beta^w_(i+j) <= sum_z tau(o,z) w(z) sum_u tau(o,u) w(u) = beta^w_j (beta^w_(i-1) + beta^w_i).
```

## Step 2: scalar coefficients are infinite above p_c

Let `p > p_c(G)` and let `w` be a weight.

**The kernel band.** First, `N = ker h` is infinite: otherwise `Gamma` would
be virtually `Z`, hence amenable. It is normal with `Gamma/N = Z` amenable,
so it is co-amenable. By `fpbs-co-amenable-subgroup-relative-threshold-is-pc`,

```text
sum_(x in N) tau(o,x) = E_p|K_o ∩ N| = infinity.
```

**The symmetrization bound.** From `w(1) <= w(1)^2` we get `w(1) >= 1`. From
`w(1) <= w(x) w(x^(-1))` and AM-GM we get

```text
w(x) + w(x^(-1)) >= 2 sqrt(w(1)) >= 2.
```

**Band 0.** `N = N^(-1)` and `tau(o,x) = tau(o,x^(-1))`, so

```text
sum_(x in N) tau(o,x) w(x) = (1/2) sum_(x in N) tau(o,x) (w(x) + w(x^(-1)))
                          >= sum_(x in N) tau(o,x) = infinity.
```

Since `N ⊆ Lambda_0`, this gives `beta^w_0 = infinity`.

**Band j.** Pick `g` with `h(g) = jK`, which exists since `h` is onto. The
map `x -> xg` sends `N` injectively into `h^(-1)(jK) ⊆ Lambda_j`. Two bounds
hold:
- by FKG and invariance, `tau(o,xg) >= tau(o,x) tau(x,xg) = tau(o,x) tau(o,g)`;
- by submultiplicativity, `w(x) <= w(xg) w(g^(-1))`.

Hence

```text
beta^w_j >= (tau(o,g) / w(g^(-1))) sum_(x in N) tau(o,x) w(x) = infinity,
```

since `tau(o,g) >= p^(|g|_S) > 0`.

**What this rules out.** This rules out every scalar closing of item 1:
- the summed form `beta^w_(i+j) <= beta^w_j (...)`;
- the pointwise form. For `y in Lambda_n`,
  `tau(o,y) w(y) <= beta^w_J sup_(u in Lambda_(n-J-1) ∪ Lambda_(n-J)) tau(o,u) w(u)`,
  using `w(y) <= w(z) w(u)`. That is,
  `a^w_n <= beta^w_J max(a^w_(n-J-1), a^w_(n-J))` for
  `a^w_n = sup_(Lambda_n) tau(o,.) w`.

Every such closing needs some `beta^w_J < 1` (or `beta^w_(J-1) + beta^w_J < 1`)
at some `p > p_c`. No weight gives this.

## Step 3: operator coefficients give the critical l2 gap

Put `rho = r_(J-1) + r_J < 1`, with `J >= 1`.

**Finiteness of the bands below J.** Let `0 <= j <= J-1`, and pick `g` with
`h(g) = (J-1-j)K`. Suppose `(x,y)` is in relative band `j`. Then `(x,yg)` is
in relative band `J-1`, and FKG gives

```text
R_(J-1)(x,yg) >= tau(x,y) tau(y,yg) = tau(o,g) R_j(x,y).
```

Right translation `(rho_g f)(y) = f(yg)` is unitary on `l^2(Gamma)`. So the
display gives `R_j <= tau(o,g)^(-1) R_(J-1) rho_g^(-1)` entrywise, and
therefore `r_j <= r_(J-1) / tau(o,g) < infinity`. So `r_0, ..., r_J` are all
finite.

**Exponential decay.** Apply Step 1 with `i = J` and `j = n - J >= 1`:

```text
r_n <= r_(n-J) (r_(J-1) + r_J) = rho r_(n-J)      for all n >= J+1.
```

So `r_n <= rho^(floor((n-1)/J)) max_(1<=k<=J) r_k`, and `sum_(j>=0) r_j < infinity`.

**The two-point operator.** Every pair `(x,y)` has either `h(y) - h(x)` or
`h(x) - h(y)` in some band `j >= 0`. Since `tau` is symmetric,

```text
T_p <= sum_(j>=0) R_j + sum_(j>=0) R_j^*   entrywise,
```

and `||T_p||_(2->2) <= 2 sum_j r_j < infinity`. So `p <= p_(2->2)`.

**The target.** Let `h(z) = m > 0`. The pair `(o,z^n)` lies in relative band
`floor(nm/K)`, and `tau(o,z^n) = <delta_o, R_j delta_(z^n)> <= r_j`. So the
target decays exponentially, and it is summable along `<z>`.

**The converse bound.** `R_j <= T_p` entrywise, so `r_j <= ||T_p||`.

**Conclusion of item 4(b).** If this happens at some `p > p_c(G)`, then
`p_c < p <= p_(2->2)`.

**Why this is at least BS.** For `p > p_u` we have `tau >= theta^2 > 0`, so
`T_p` is unbounded. Hence `p_(2->2) <= p_u`, and `p_c < p_(2->2)` implies
`p_c < p_u`.

## Step 4: calibration on T_4

Take `Gamma = F_2 = <a,b>`, `h(a) = 1`, `h(b) = 0`, so `K = 1`. Then
`tau(x,y) = p^(d(x,y))`, `p_c = 1/3` and `p_(2->2) = 1/sqrt 3`.

**The operator route works below `1/sqrt 3`.** `R_j` is right convolution by
`f_j = p^(|u|) 1{h(u) = j}`, which is supported on `|u| >= j`. On the sphere
`S_n` we have `||f_j 1_(S_n)||_2 <= p^n (4 * 3^(n-1))^(1/2)`. Haagerup's
inequality `||lambda(f)|| <= sum_n (n+1) ||f 1_(S_n)||_2` then gives

```text
r_j <= sum_(n>=j) 2 (n+1) (p sqrt 3)^n -> 0       for p < 1/sqrt 3.
```

So `r_(J-1) + r_J < 1` for large `J`, and the route of Step 3 runs on the
whole window `(1/3, 1/sqrt 3)`.

**Every scalar coefficient is infinite above `1/3`.** This is Step 2
specialized. Here `N` is the normal closure of `b`, which is free of infinite
rank.

**The half-space variant is also infinite.** Take the half-space coefficient
`beta^hs_J`, which counts reduced words that end with `a` at height `J` and
whose proper prefixes all have height `< J`. Under the uniform measure on
reduced words of length `n`, the height is a zero-drift Markov additive
process. The ballot constraint therefore costs a polynomial factor
`n^(-O(1))`. Such words number `3^n n^(-O(1))`, and `beta^hs_J = infinity`
for `p > 1/3`.

This paragraph is a heuristic count, not a proof. It is used only for
calibration.
