---
rg: 2
id: leavitt-triangular-units-have-linear-depth-growth
kind: claim
title: Infinite-order binary Leavitt units conjugate into the nonpositive or nonnegative degree part have linearly growing depth
distinct_from:
  depth-monotone-leavitt-subalgebras-are-stably-finite: that proves the degree-monotone subalgebras are stably finite and their unit groups locally residually finite; this proves linear depth growth for their infinite-order units and conjugates.
  leavitt-free-group-leading-term-forces-linear-depth: that is a leading-term criterion for one order at a time; this is a whole subgroup handled through Frobenius squaring of a unipotent power.
---

**ESTABLISHED** by `leavitt-triangular-units-have-linear-depth-growth-proof`.

Let `R = L_(F_2)(1,2)` with the `Z`-grading `deg s_i = 1`, `deg t_i = -1`. Put
`H_<= = { u : u, u^(-1) in ⊕_(k <= 0) R_k }` and define `H_>=` in the same way. These are the groups `H^1_<=`
and `H^1_>=` of `depth-monotone-leavitt-subalgebras-are-stably-finite`. They contain the level part of `V`,
every level transvection and every depth-decreasing transvection (respectively, every depth-increasing one).

**Claim.** Suppose `u` in `R^x` has infinite order and `h u h^(-1)` lies in `H_<=` or `H_>=` for some `h`.
Then `lambda(u) >= 1/r > 0`, where `r` is the order of the degree-zero component of `h u h^(-1)` in
`R_0 = ⋃_n M_(2^n)(F_2)`.

In particular no Heisenberg center and no `BS(1,k)` base, `|k| >= 2`, is conjugate into `H_<=` or `H_>=`
(`no-heisenberg-from-linear-depth-growth`, steps 2 and 3).
