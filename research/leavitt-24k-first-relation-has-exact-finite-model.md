---
rg: 2
id: leavitt-24k-first-relation-has-exact-finite-model
kind: claim
title: The first 24k relation forces a large commutator but has an exact GL3(F8) solution
distinct_from:
  binary-leavitt-hyperlinear-iff-24k-feasible: that is the equivalence between hyperlinearity and vanishing of every Delta_m; this evaluates the first nontrivial relation, gives the lower bound it forces, and shows that relation alone admits an exact model.
  leavitt-24k-feasibility-has-a-uniform-gap: that asks for a positive uniform lower bound on some Delta_m, which would prove nonhyperlinearity; this proves that the first relation is not such an m.
artifacts:
  - research/artifacts/leavitt-24k-relative-unitary-reduction-2026-09-08.md
---

**ESTABLISHED.**  In the notation of `binary-leavitt-hyperlinear-iff-24k-feasible`
put

```text
d = [b_2, c b_1 c^(-1)],   a = [d, c^2 d c^(-2)],   b = c d c^(-1),
z = a b a^(-1),            r_* = z c z c,                        (LR1)
```

whose images in `H` are `x_13(1), x_12(1), x_21(1)`, the transposition
`(12)`, and `1`; so `r_*` lies in `ker q` and belongs to every `T_m`.

**Necessary bound.**  For every `k` and every `U in U(24k)`,

```text
|| [pi(b_2), C_k pi(b_1) C_k^*] - I ||_2
        >= ( sqrt 2 - ||pi(r_*) - I||_2 ) / 2.                   (LR2)
```

So any solution sequence must keep that commutator at normalized distance
`1/sqrt 2 - o(1)` from the identity; in particular `U = I` fails, since then
the two frozen factors commute, the commutator is `I`, and
`pi(r_*) = C_k^2` is at distance `sqrt 2`.

**But this relation alone is satisfiable exactly.**  In
`GL_3(F_8)` with `F_8 = F_2[alpha]/(alpha^3 + alpha + 1)` take the same
3-cycle `c` and

```text
b_1' = x_12(alpha),    b_2' = x_12(alpha^(-1)),   b_3' = x_12(1),
alpha^(-1) = alpha^2 + 1.                                        (LR3)
```

Then `1, alpha, alpha^(-1)` are `F_2`-independent, so these generate `C_2^3`;
the computation `(LR1)` uses only `alpha^(-1) alpha = 1` and again gives
`r_* = 1` exactly.  The left regular representation of `GL_3(F_8)`, of
dimension `115379712 = 24 * 4807488`, restricts on each of the two finite
subgroups to a multiple of that subgroup's regular representation, so after a
basis change it is one of the models `(LK2)` with `pi(r_*) = I` exactly.

Hence `(LR2)` is a genuine constraint on the relative unitary and **not** an
obstruction: no nonhyperlinearity conclusion can be drawn from the first
relation.  The `F_8` assignment does not extend to a ring map from `R` --
`(LG2)` would force `s_1 = s_0` and `t_1 = t_0`, contradicting `t_0 s_1 = 0`
-- so it is a model of the displayed relation only, not of `H`.
