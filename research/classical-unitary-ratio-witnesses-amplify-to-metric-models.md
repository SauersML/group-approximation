---
rg: 2
id: classical-unitary-ratio-witnesses-amplify-to-metric-models
kind: claim
title: Unnormalized ratio witnesses in the operator, Hilbert--Schmidt or rank length amplify to metric models, so for Thompson's V they are exactly MF, hyperlinearity and unitary rank approximability
distinct_from:
  thompson-v-has-unbounded-compact-unitary-relator-width: that is the width statement, which any conjugation-invariant length certifies; this shows that the three classical lengths certify it only through the corresponding metric approximation property of V.
  balanced-replica-hs-amplification: that is the trace lemma for one balanced tensor power; this uses it, together with a second case and a rank analogue, to turn vanishing-ratio models with no lower bound into constant-separation models.
  adaptive-tensor-amplification: that converts operator separation into 2-norm separation at a dimension-dependent cost; this keeps the length fixed and pays only a constant factor in the defect.
  tensor-power-deficiency-amplification-loses-common-return: that is a no-go for kernel returns of rectangular amplification; this is a positive amplification of eigenvalue measures of unitaries.
artifacts:
  - experiments/ratio-witness-amplification-2026-09-17/check_amplification.py
  - experiments/ratio-witness-amplification-2026-09-17/output.txt
---

**ESTABLISHED** by `classical-unitary-ratio-witnesses-amplify-to-metric-models-proof`.

**Lengths.** On `U(d)` put, with `tau` the normalized trace,

```text
l_op(g)   = ||g - I||_op,
l_2(g)    = tau((g - I)^*(g - I))^(1/2)      (normalized Hilbert--Schmidt),
l_rk(g)   = rank(g - I) / d                  (normalized rank).
```

Ratios do not see normalization, so "unnormalized" and "normalized" ratio models coincide.

**Setting.** `Gamma = <S | R>` is a countable presented group and `a in F(S)`. Say `a` has an
**`l`-ratio witness** if for every finite `R_0 <= R` and every `epsilon > 0` there are `d` and
`U in U(d)^S` with `a(U) != I` and

```text
l(r(U)) <= epsilon * l(a(U))      for every r in R_0.                         (W)
```

No lower bound on `l(a(U))` is assumed; it may tend to `0` along the witnesses.

## Statement

**(A) Amplification.** Let `U in U(d)^S` satisfy (W) for a finite set `R_0` with some `epsilon <= 1`.

- **(op)** There is a `k >= 1` such that `W = U^(tensor k)` satisfies
  `l_op(a(W)) >= sqrt 2` and `l_op(r(W)) <= 4 epsilon` for `r in R_0`.
- **(HS)** There is a tuple `W`, equal to `U^(tensor k)` or to `(U tensor conj U)^(tensor k)`, with
  `l_2(a(W))^2 >= 2(1 - e^-1)` and `l_2(r(W)) <= 5 epsilon` for `r in R_0`.
- **(rank)** There is a `k >= 1` such that `W = U^(tensor k)` satisfies
  `l_rk(a(W)) >= 1/4` and `l_rk(r(W)) <= 4 epsilon` for `r in R_0`.

Each amplification applies one continuous homomorphism `Phi: U(d) -> U(d')` coordinatewise, so
`w(W) = Phi(w(U))` for every word `w`.

**(B) Radicals.** Consequently `a` has an `l_op`-, `l_2`- or `l_rk`-ratio witness iff there is a
homomorphism from `Gamma` into, respectively,

- the operator-norm ultraproduct `prod_omega U(d_m) / {l_op -> 0}`,
- the tracial ultraproduct `prod_omega U(d_m) / {l_2 -> 0}`,
- the rank ultraproduct `prod_omega U(d_m) / {l_rk -> 0}`,

that does not kill `a`. The converse direction is immediate.

**(C) Thompson's group V.** `V` is simple (`thompson-v-finitely-presented-infinite-simple`). So some nontrivial
`a` has a witness in the length

- `l_op` iff `V` is MF, in the unitary-sequence corona sense of `countable-group-mf-conventions`;
- `l_2` iff `V` is hyperlinear (`thompson-v-hyperlinear`);
- `l_rk` iff `V` embeds in a rank ultraproduct of unitary groups. Since `U(d) <= GL_d(C)` carries the same rank metric,
  that makes `V` linear sofic over `C`.

## What this kills

Part (C) of `kl-kernel-lies-in-the-compact-unitary-width-radical` lets any conjugation-invariant subadditive length certify
`thompson-v-has-unbounded-compact-unitary-relator-width`. That node, and `kl-violating-equation-over-thompson-v`, recorded
unitary rank and Hilbert--Schmidt ratio models as a new format, not reduced to an open approximation question. The belief was
that eigenvalue products can cancel in tensor powers.

That belief is false.

- **The invariant.** It is the eigenvalue measure `mu` of `a(U)` on the circle, whose `k`-th convolution power is the
  eigenvalue measure of `a(U^(tensor k))`.
  - Cancellation can only return mass to the identity eigenvalue in alternate steps: `p_j + p_(j+1) <= 1` for the no-atom part.
  - In trace it can only rotate, not shrink, the trace. The balanced replica `U tensor conj U` removes the rotation, and a
    power of `U` itself exploits it.
- **Where every member dies.** Every such witness dies at the amplification step (A): once amplified, it is a
  constant-separation metric model. So a ratio witness for `V` in any of the three classical lengths is exactly as hard as
  the corresponding one of the open claims
  - `V` MF,
  - `thompson-v-hyperlinear`,
  - `V` unitarily rank-approximable.

  This holds whether or not the defect of `a` tends to zero.

A certificate of `thompson-v-has-unbounded-compact-unitary-relator-width` that avoids those three questions therefore
has to use one of the following:

1. a length outside `{l_op, l_2, l_rk}`, such as a Schatten `p`-norm with `p` not in `{2, infinity}`, which is not covered
   here;
2. a length that depends on the model, such as the conjugacy word length of the relator images themselves;
3. a non-metric argument.
