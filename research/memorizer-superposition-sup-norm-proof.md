---
rg: 2
id: memorizer-superposition-sup-norm-proof
kind: route
title: Evaluate the memorizers at the linear points, where they are the F_2 characters, and apply Parseval
target: memorizer-superposition-has-large-sup-norm
requires: []
---

The whole proof is that the memorizers become characters on a set of `N`
points, so a sup norm over the cube dominates an `L^2` norm over `F_2^k`.

**Values at linear points.**  For `t in F_2^k` let `chi_t in {-1,1}^Omega`
be the assignment `(chi_t)_u = (-1)^{<t,u>}`.  Then
`(chi_t)_0 = 1`, and for every pair `{u, u+b}`

```text
(chi_t)_u (chi_t)_{u+b} = (-1)^{<t,u> + <t,u+b>} = (-1)^{<t,b>},
```

independently of `u`.  So every one of the `M` products in `B_{b,r}` equals
`(-1)^{r<t,b>}`, which is `(-1)^{<t,b>}` because `r` is odd, the average
over `A` is the same value, and

```text
B_{b,r}(chi_t) = (-1)^{<t,b>}.                                          (L1)
```

**Parseval.**  Let `B subset Omega \ {0}` and let `c_b` be real.  Define
`h : Omega -> R` by `h(b) = c_b` for `b in B` and `h = 0` elsewhere.  By
`(L1)`,

```text
sum_{b in B} c_b B_{b,r}(chi_t) = sum_{b in Omega} h(b) (-1)^{<t,b>} = N * hat h(t),
```

with `hat h(t) = (1/N) sum_b h(b) (-1)^{<t,b>}`.  Parseval on `F_2^k` gives
`sum_t |hat h(t)|^2 = (1/N) sum_b h(b)^2`, so

```text
(1/N) * sum_{t in F_2^k} | sum_{b in B} c_b B_{b,r}(chi_t) |^2
   = N * sum_t |hat h(t)|^2 = sum_{b in B} c_b^2.
```

The left side is an average of `|F|^2` over `N` points of the cube, so it
is at most `||F||_infty^2`.  This is `(S1)`:

```text
|| sum_{b in B} c_b B_{b,r} ||_infty >= ( sum_{b in B} c_b^2 )^(1/2).
```

With `|c_b| >= delta` throughout `B` the right side is `delta * |B|^(1/2)`,
which is `(S2)`.

**The exact value at the all-ones point.**  Taking `t = 0` gives
`chi_0 = (1,...,1)` and `B_{b,r}(chi_0) = 1` for every `b`, so with
`B = Omega \ {0}` and all `c_b = 1` the superposition takes the value
`N-1` there.  The triangle inequality with `(M1)` gives
`|P_s| <= N-1` everywhere, so the sup norm is exactly `N-1`.

**Consequence.**  A normalization `lambda * sum_{b in B} c_b B_{b,r}` with
sup norm at most `1` has, by `(S2)`, every quotient dictator coefficient
`|lambda c_b| <= |B|^(-1/2)`.  On a direction set of density `alpha` this is
`(alpha(N-1))^(-1/2) -> 0`, so no member of the linear span of the pair
memorizers is a bounded function with dimension-free heaviness in a
positive density of directions.
