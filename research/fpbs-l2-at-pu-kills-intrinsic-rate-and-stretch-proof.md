---
rg: 2
id: fpbs-l2-at-pu-kills-intrinsic-rate-and-stretch-proof
kind: route
title: Evaluate the log-Lipschitz bound Lambda(t) <= log(t/p_(2->2)) at p_u, test the truncated kernel on balls, and import p_(2->2) = p_u on tree products
target: fpbs-l2-at-pu-kills-intrinsic-rate-and-stretch
requires:
  - fpbs-intrinsic-rates-log-lipschitz-in-parameter
  - fpbs-intrinsic-l2-rate-closed-zero-set
  - fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu
---

Complete written proof. No computation is used. Notation as in the target.

## Inputs

**(L)** Item 3 of `fpbs-intrinsic-rates-log-lipschitz-in-parameter`: for
every `t in [0,1]`,

```text
Lambda(t) <= max(0, log(t / p_(2->2))).
```

**(F)** Item 1 of `fpbs-intrinsic-l2-rate-closed-zero-set`. The limit
`Lambda(t) = lim_R a_R(t)/R` exists, where `a_R(t) = log||T^(R)_t||_(2->2)`.
This part is proved there by BK and Fekete, and does not use the flagged
Step 2 sentence.

**(HP)** `fpbs-hutchcroft-pan-tree-times-amenable-l2-threshold-is-pu`. On
`T x Z^d` (`k >= 3`, `d >= 1`), `0 < p_c < p_u < 1` and `p_(2->2) = p_u`. On
`T x H` and `LL(T)`, `p_(2->2) = p_u`.

## Step 1. Item 1 (general implication)

Suppose `Lambda(p_u) > 0`. Then the maximum in (L) at `t = p_u` is attained
by the logarithm, so `0 < Lambda(p_u) <= log(p_u/p_(2->2))`. Exponentiating,
`p_u >= p_(2->2) e^(Lambda(p_u)) > p_(2->2)`. ∎

## Step 2. Item 2 (vanishing)

Let `p_(2->2) = p_u` and `t >= p_u`. Then `log(t/p_(2->2)) = log(t/p_u) >= 0`,
so (L) reads `Lambda(t) <= log(t/p_u)`. At `t = p_u` this gives
`Lambda(p_u) <= 0`, and `Lambda >= 0` because the kernels have nonnegative
entries and nonzero diagonal. ∎

## Step 3. Ball test: an averaged stretch constant bounds Lambda below

Let `K` be an averaged stretch constant at `t`, with constant `c > 0`. Fix
`m >= 1` and put `R_m = ceil(K(2m+1))` and `f = 1_(B_m)`.

- `T^(R)_t` is entrywise nondecreasing in `R`.
- Its entries lie in `[0,1]` and vanish when `d(u,v) > R`. So it is a bounded
  operator, with norm at most `|B_R|`.
- Therefore

  ```text
  ||T^(R_m)_t||  >=  <f, T^(R_m)_t f> / ||f||_2^2
                 >=  (1/|B_m|) sum_(u,v in B_m) P_t(d_omega(u,v) <= K(2m+1))
                 >=  c |B_m|.
  ```

So `a_(R_m)(t) >= log c + log|B_m|`. Divide by `R_m <= K(2m+1) + 1` and let
`m -> infinity`. By (F), `a_(R_m)/R_m -> Lambda(t)`, while
`log|B_m| / m -> log gr`. Hence

```text
Lambda(t)  >=  log(gr) / (2K).
```

A linear stretch constant `K` at `t` is an averaged one with
`c = inf_(u,v) P_t(d_omega(u,v) <= K(d(u,v)+1))`. The reason is that
`d(u,v) <= 2m` on `B_m`, and the event is monotone in the radius. ∎

## Step 4. Item 3 (stretch blow-up)

Let `p_(2->2) = p_u < 1`, and let `t in (p_u,1]` carry an averaged stretch
constant `K`. By Steps 3 and 2,

```text
log(gr)/(2K)  <=  Lambda(t)  <=  log(t/p_u).
```

Here `log(t/p_u) > 0` and `gr > 1`, so `K >= log(gr) / (2 log(t/p_u))`. Since
`log x <= x - 1`, we have `log(t/p_u) <= (t - p_u)/p_u`, which gives the second
bound. The right-hand side tends to infinity as `t ↓ p_u`. So no `K` serves a
whole interval `(p_u, p_u+eps)`, and `K_*(t) -> infinity`. ∎

## Step 5. Item 4 (counterexamples)

**The graph is a Cayley graph of a nonamenable group.**

- `(Z/2)^{*k}` on its `k` standard involutions has as Cayley graph the
  `k`-regular tree. It is simple, since distinct involutions give distinct
  neighbours and the group is a free product.
- `Z^d` on `{±e_i}` gives the lattice.
- The union of the two generating sets, inside the direct product, gives the
  Cartesian product graph. That is the product in (HP).
- The group is nonamenable because `(Z/2)^{*k}` is nonamenable for `k >= 3`
  and is a quotient of it.

For `k = 4`, `Cay(F_2, {a^±, b^±})` is the same 4-regular tree, which gives
the standard Cayley graph of `F_2 x Z^d`.

**The conclusions.** By (HP), `p_u < 1` and `p_(2->2) = p_u`.

- Step 2 gives `Lambda(p_u) = 0`. This contradicts (IL2), which asserts
  `Lambda(p_u) > 0` for every nonamenable Cayley graph with `p_u < 1`.
- Step 4 shows that no `K` is a linear stretch constant at every `t > p_u`.
  This contradicts (UCS), which asserts `sup_(t>p_u) K_*(t) < infinity`
  under the same hypotheses.
- Step 4 applied to averaged constants refutes the averaged hypothesis of
  `fpbs-intrinsic-l2-rate-via-uniform-stretch`.

For `T x H` and `LL(T)`, (HP) gives `p_(2->2) = p_u`, and the same steps
apply whenever `p_u < 1`. ∎

## Step 6. Class obstruction

Let `0 <= K_R <= T^(R)_t` entrywise. For nonnegative matrices,
`||K_R||_(2->2) <= ||T^(R)_t||_(2->2)`, because
`|<g, K_R h>| <= <|g|, K_R |h|> <= <|g|, T^(R)_t |h|>`.

So any exponential lower bound `||K_R|| >= e^(delta R)` at `t` gives
`Lambda(t) >= delta`. At `t = p_u`, or uniformly on `(p_u, p_u+eps)` by
continuity (item 2 of the log-Lipschitz claim), it gives `Lambda(p_u) > 0`.

By Step 1 that forces `p_(2->2) < p_u`. By (HP) this is false on `T x Z^d`,
where nonetheless `p_c < p_u`. ∎
