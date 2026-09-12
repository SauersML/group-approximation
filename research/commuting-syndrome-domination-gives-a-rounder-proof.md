---
rg: 2
id: commuting-syndrome-domination-gives-a-rounder-proof
kind: route
title: Read the cost clause off the joint syndrome measurement
target: commuting-syndrome-domination-gives-a-rounder
requires: []
---

Because `B_1,...,B_m` commute they admit a joint projective measurement, and
its outcome determines the classical set `S = {a : B_a = 1}` with
`|S| = sum_a 1[a in S]`.  Writing `rho' = W rho W^*`, which is a state since
`W` is an isometry,

```text
E|S| = sum_a Pr[a in S] = sum_a Tr(B_a rho') = Tr[ W^*(sum_a B_a) W rho ].
```

Applying (SD) to the state `rho` bounds the right side by
`C sum_a Tr(h_a rho)`, which is clause (2) of the rounder definition.
Clause (1) is (EX) verbatim, using that `h_a >= 0` and `sigma_S >= 0` make
`h_a sigma_S = 0` and `Tr(h_a sigma_S) = 0` equivalent.

For the converse remark in the claim: if the cost clause holds for every
input state, then `Tr[W^*(sum_a B_a)W rho] <= C Tr[(sum_a h_a) rho]` for all
`rho`, and states span the self-adjoint part, so (SD) follows as an operator
inequality.

For the local form, sum (SD2) over `j` and use `h_a >= 0`:

```text
sum_j W^* B_j W <= C_0 sum_j sum_(a in N(j)) h_a
                <= C_0 R sum_a h_a,
```

the last step because each `a` occurs in at most `R` neighbourhoods.  The
state-evaluated version of the same two lines is
`bounded-overlap-syndrome-energy-accounting`.
