---
rg: 2
id: fpbs-normal-subgroup-half-growth-floor-proof
kind: route
title: Count the conjugates of one element of the normal subgroup by the ball, modulo its centralizer, and sum by parts
target: fpbs-normal-subgroup-half-growth-floor
requires: []
---

Notation is as in the target. Put `l = |n0|`.

**Step 1 (conjugate map).** Define `phi : B_r -> Gamma` by
`phi(g) = g n0 g^(-1)`.

- Since `N` is normal, `phi(g) ∈ N`.
- `|phi(g)| <= 2|g| + l <= 2r + l`.

So `phi(B_r) ⊂ N ∩ B_(2r+l)`.

**Step 2 (fibres).** If `g, g' ∈ B_r` and `phi(g) = phi(g')`, then `g^(-1) g'`
commutes with `n0`. So `g' = g z` with `z ∈ C`, and
`|z| <= |g| + |g'| <= 2r`. Each fibre of `phi` therefore lies in
`g (C ∩ B_(2r))`, and it has at most `|C ∩ B_(2r)|` points. Hence

```text
|N ∩ B_(2r+l)| >= |phi(B_r)| >= |B_r| / |C ∩ B_(2r)|.
```

**Step 3 (volume).** Since `|B_(r+s)| <= |B_r| |B_s|`, Fekete's lemma gives
`gr = inf_r |B_r|^(1/r)`. So `|B_r| >= gr^r`. This proves the displayed
inequality.

**Step 4 (floor).** Fix `eps > 0`. For all large `r`,
`|C ∩ B_(2r)| <= (c + eps)^(2r)`. Therefore

```text
|N ∩ B_(2r+l)|^(1/(2r+l)) >= ( gr^r (c+eps)^(-2r) )^(1/(2r+l)).
```

The right-hand side tends to `sqrt(gr)/(c+eps)`. For
`2r+l <= R <= 2r+l+1`, monotonicity of `R -> |N ∩ B_R|` gives the same bound up
to a factor that tends to 1. Letting `eps -> 0` proves (1).

**Step 5 (divergence).** Put `A_R = |N ∩ B_R|` and `b_R = gr^(-R/2)`, which is
nonincreasing because `gr >= 1`. Summation by parts gives

```text
sum_(n ∈ N, |n| <= M) b_|n|
   = sum_(R <= M) (A_R - A_(R-1)) b_R
   >= sum_(R <= M) A_R (b_R - b_(R+1))
    = (1 - gr^(-1/2)) sum_(R <= M) A_R gr^(-R/2).
```

Here `A_(-1) = 0`, and the dropped boundary term `A_M b_(M+1)` is nonnegative.
Statement (2) assumes `gr > 1`, which holds whenever `Gamma` is nonamenable.

Take `R = 2r + l`. Under `|C ∩ B_R| <= A R`, Steps 2 and 3 give

```text
A_R gr^(-R/2) >= gr^r / (2 A r) · gr^(-r - l/2) = gr^(-l/2) / (2 A r).
```

Summing over `r >= 1` diverges like the harmonic series. So
`sum_(n ∈ N) gr^(-|n|/2) = infinity`, which proves (2). ∎

**Scope of Step 5.** The linear bound on the centralizer is used exactly once.

- With `|C ∩ B_R| ~ R^2`, for example a central `Z^2` or a distorted cyclic
  centralizer in a Heisenberg group, the lower bound is summable and (2) is
  inconclusive.
- With exponential centralizer growth, (1) is the only information.
