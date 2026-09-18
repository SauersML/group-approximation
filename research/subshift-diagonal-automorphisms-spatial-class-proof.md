---
rg: 2
id: subshift-diagonal-automorphisms-spatial-class-proof
kind: route
title: Stone duality, monomial normalizers and full-group units reduce a finite spatial class to a gauge automorphism; word complexity kills dilations
target: subshift-diagonal-automorphisms-need-infinite-spatial-class
requires:
  - minimal-subshift-algebra-is-simple-lef-ring
  - virtually-inner-ring-automorphisms-fail-centralizer-compression
---

## Why sufficient

Notation as in the target.  Every element of `S` is uniquely `sum_n f_n u^n`
with `f_n in D`, finitely many nonzero.  The rule `u^n f = (f o T^{-n}) u^n`
gives `u^n 1_A = 1_(T^n A) u^n`.  `X` has no periodic points, because it is
infinite and minimal.

**Step 1 (spatial homeomorphism).**  The idempotents of `D` are exactly the
indicators `1_A` of clopen sets `A`, because an idempotent `F_q`-valued
function takes values in `{0,1}`.  `sigma` permutes them, preserves products,
and maps `1 - 1_A` to `1 - sigma(1_A)`.  So it is an automorphism of the
Boolean algebra of clopen sets, and Stone duality gives a unique homeomorphism
`phi = phi_sigma` with `sigma(1_A) = 1_(phi(A))`.  Composites compose, which
gives `phi_(sigma tau) = phi_sigma phi_tau`.

**Step 2 (normalizer units are monomial).**  Let `w in S^x` with
`w D w^{-1} = D`, and write `w = sum_(n in F) f_n u^n` with every `f_n != 0`.
Let `A_n` be the support of `f_n`, a clopen set.
- For a clopen `A`, `e' = w 1_A w^{-1}` is an idempotent of `D`, say `1_(A')`.
  Comparing the coefficients of `u^n` in `w 1_A = e' w` gives
  `f_n 1_(T^n A) = 1_(A') f_n` for every `n`.
- If `x in A_n cap A_m` with `n != m`, then for every clopen `A`,
  `x in T^n A` iff `x in A'` iff `x in T^m A`.  So `T^{-n} x` and `T^{-m} x`
  lie in the same clopen sets, hence are equal, and `x` is periodic.  That is
  impossible, so the `A_n` are pairwise disjoint.
- `w^{-1}` also normalizes `D`, so it too is `sum g_m u^m` with disjoint
  supports.  The coefficient of `u^0` in `w w^{-1} = 1` is
  `sum_n f_n (g_(-n) o T^{-n}) = 1`, so the `A_n` cover `X`.

Therefore `w = c u_nu`, with `c = sum_n f_n in LC(X, F_q^x)` and
`u_nu = sum_n 1_(A_n) u^n = c^{-1} w`, a unit.  Define
`beta(x) = T^{-n} x` for `x in A_n`.  Then `u_nu f = (f o beta) u_nu`, so
`Ad(u_nu)` acts on `D` as `f -> f o beta`.  That is an automorphism of `D`,
so `beta` is a homeomorphism: clopen sets separate points, and a point outside
the closed set `beta(X)` would give a nonzero indicator pulling back to `0`.
By construction `beta in [[T]]`.

**Step 3 (item 2 and item 1).**  `sigma(u) D sigma(u)^{-1} = sigma(u D u^{-1})
= D`, so Step 2 gives item 2, with some `beta`.  Now apply `sigma` to
`u 1_A u^{-1} = 1_(TA)`:

```text
1_(phi T A) = sigma(1_(TA)) = c u_nu 1_(phi A) u_nu^{-1} c^{-1}
            = 1_(phi A) o beta = 1_(beta^{-1} phi A).
```

So `phi T = beta^{-1} phi`, that is `phi T phi^{-1} = beta^{-1}`.  This lies
in `[[T]]`: the cocycle of `beta^{-1}` is `n` on the clopen set
`beta(A_n) = T^{-n} A_n`, so it is continuous.

**Step 4 (full-group units).**  Let `g in [[T]]`, with `g(x) = T^(m(x)) x`,
and let `B_m = {m(x) = m}`, a finite clopen partition.  The sets `T^m B_m`
also partition `X`, because `g` is a bijection.  Put

```text
v_g = sum_m 1_(T^m B_m) u^m,        v_g' = sum_m 1_(B_m) u^(-m).
```

Then `v_g v_g' = sum_(m,m') 1_(T^m B_m) 1_(T^m B_(m')) u^(m-m') = sum_m
1_(T^m B_m) = 1`, since the `B_m` are disjoint.  Also `v_g' v_g =
sum_(m,m') 1_(B_m) 1_(T^(m'-m) B_(m')) u^(m'-m)`.  If `x in B_m` and
`y = T^(m-m') x in B_(m')`, then `g(y) = T^m x = g(x)`, so `y = x` and
`m = m'` by aperiodicity.  So `v_g' v_g = 1`.  Finally `v_g f v_g^{-1}` takes
the value `f(T^{-m} y) = f(g^{-1} y)` at `y in T^m B_m`.  So `Ad(v_g)` is
`f -> f o g^{-1}` on `D`: it is diagonal-preserving with `phi_(Ad v_g) = g`.

**Step 5 (trivial spatial class gives order dividing q - 1 modulo inner).**
Suppose `sigma` is `F_q`-linear and `phi_sigma in [[T]]`.  Put
`sigma_1 = Ad(v_(phi_sigma))^{-1} sigma`, so `phi_(sigma_1) = id` by Step 1.
`sigma_1` fixes every idempotent of `D`, and being `F_q`-linear it fixes `D`
pointwise.  By Step 3, `sigma_1(u) = c u_nu` with `beta^{-1} = T`.  So
`T^{-n} x = T^{-1} x` on `A_n`, and aperiodicity forces `A_n = empty` unless
`n = 1`.  Hence `u_nu = u` and `sigma_1(u) = c u` with
`c in LC(X, F_q^x)`.  Since `sigma_1` fixes `c`, induction gives
`sigma_1^j(u) = c^j u`.  So `sigma_1^(q-1)` fixes `D`, `u` and
`u^{-1} = (c^(q-1) u)^{-1}`, which generate `S`; hence `sigma_1^(q-1) = id`.

The inner automorphisms `Ad(v)`, `v in S^x`, form a normal subgroup of
`Aut(S)`, because `tau Ad(v) tau^{-1} = Ad(tau(v))`.  Modulo it, `sigma`
equals `sigma_1`, so `sigma^(q-1)` is inner.

**Step 6 (item 3).**  By `minimal-subshift-algebra-is-simple-lef-ring`
(item 2), the centre of `S` is `F_q`.  `sigma` preserves the centre and acts
on it by a field automorphism, whose order divides `e`.  So `sigma^e` is
`F_q`-linear.  If `phi_sigma^r in [[T]]`, then `tau = sigma^(e r)` is
`F_q`-linear with `phi_tau = phi_sigma^(e r) in [[T]]`, by Step 1 and because
`[[T]]` is a group.  By Step 5, `tau^(q-1) = sigma^(e r (q-1))` is inner.

By item 3 of `minimal-subshift-algebra-is-simple-lef-ring`, `S` embeds
injectively and unitally in an algebraic ultraproduct of `M_(N_k)(F_q)`.  So
`virtually-inner-ring-automorphisms-fail-centralizer-compression` applies,
with `T = S` and `m = e r (q-1)`, and (G2) fails.

**Step 7 (item 4: an infinite subshift is not conjugate to a power).**
Suppose `h = phi_sigma` satisfies `h T h^{-1} = T^k` with `|k| >= 2`, so
`h T = T^k h`.  Let `A` be the alphabet, `L_n` the set of words of length `n`
occurring in `X`, and `p(n) = |L_n|`.
- *Monotone.*  Every word of `X` extends to the right inside `X`, so dropping
  the last letter maps `L_(n+1)` onto `L_n`, and `p(n+1) >= p(n)`.
- *Block bound.*  `h` is uniformly continuous on the compact space `X`, so
  there is `r` such that `h(x)_s` depends only on `x_([-r,r])` for each of the
  finitely many `s` with `0 <= s < |k|`.  Iterating `h T = T^k h` gives
  `h T^j = T^(kj) h`.  For `i = k j + s` with `0 <= s < |k|`,

  ```text
  h(x)_i = (T^i h x)_0 = (T^s T^(kj) h x)_0 = (T^s h(T^j x))_0 = h(T^j x)_s ,
  ```

  which depends only on `x_([j-r, j+r])`.  As `i` runs over `[0, |k| n)`, `j`
  runs over an interval of `n` integers.  So `h(x)_([0,|k|n))` is a function
  of a window of `x` of length `n + 2r`.  `h` is onto `X` and `X` is
  shift-invariant, so every word of `L_(|k| n)` occurs as some
  `h(x)_([0,|k|n))`.  Hence `p(|k| n) <= p(n + 2r)`.
- *Eventually constant.*  For `n >= 2r`, `|k| n >= 2n >= n + 2r`, so
  monotonicity gives `p(|k| n) = p(n + 2r)` and `p` is constant on
  `[n + 2r, 2n]`.  For `n >= 2r + 1`, consecutive intervals overlap, so `p` is
  constant, say `p(n) = P`, on `[4r + 2, infinity)`.
- *Finite.*  Take `n >= 4r + 2`.  `p(n+1) = p(n)` makes both "drop the last
  letter" and "drop the first letter" bijections `L_(n+1) -> L_n`.  So each
  word of length `n` has a unique extension to either side, and by induction
  `x_([0,n))` determines `x`.  Hence `|X| <= P`, contradicting that `X` is
  infinite.

If `sigma(u) in D^x u^k`, then `u_nu = u^k`, so `beta = T^{-k}` and
`phi_sigma T phi_sigma^{-1} = beta^{-1} = T^k` by Step 3.  This is excluded
for `|k| >= 2`.

## Why each step is needed

- Steps 1 to 3 attach a spatial class to `sigma`, and they are where
  aperiodicity of the minimal subshift enters.
- Steps 4 to 6 convert a finite spatial class into an inner power.  Gauge
  cocycles have exponent `q - 1` and Frobenius has order `e`, so the power is
  explicit.
- Step 7 is independent of approximation.  It shows the natural "squaring"
  candidate on `u` is not even an automorphism, so no model argument is
  needed for it.
