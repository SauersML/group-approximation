---
rg: 2
id: schatten-p-ratio-data-defeat-tensor-replica-amplification
kind: claim
title: For Schatten p other than 2 and infinity, eigenvalue data of a ratio witness can defeat every tensor-replica amplification and every classical comparison
distinct_from:
  classical-unitary-ratio-witnesses-amplify-to-metric-models: that is the positive amplification theorem for the operator, Hilbert--Schmidt and rank lengths; this shows that its method, convolution of eigenvalue measures under tensor replicas, cannot handle normalized Schatten-p lengths for p not in {2, infinity}, and names the scale mismatch that stops it.
  thompson-v-has-unbounded-compact-unitary-relator-width: that is the open width statement; this is a method-level class kill for one surviving witness format of it, and decides nothing about V.
  balanced-replica-hs-amplification: that is the trace lemma behind the p = 2 case; this explains why no analogue exists for p != 2 at the level of eigenvalue measures.
artifacts:
  - experiments/schatten-p-tensor-replica-2026-09-17/check_schatten_replicas.py
  - experiments/schatten-p-tensor-replica-2026-09-17/output.txt
---

**ESTABLISHED** by `schatten-p-ratio-data-defeat-tensor-replica-amplification-proof`. It is a statement about
probability measures on the circle, so it decides nothing about Thompson's group `V`. What it kills is the
spectral amplification method.

## Notation

`T` is the unit circle. For a probability measure `mu` on `T` put

```text
L_p(mu)  = ( int |lambda - 1|^p dmu )^(1/p)        (1 <= p < infinity),
L_op(mu) = max { |lambda - 1| : lambda in supp mu },
L_rk(mu) = mu(T \ {1}).
```

For `g in U(d)` with normalized eigenvalue measure `mu_g`, these are the normalized Schatten-`p`, operator and rank
lengths of `g`. `L_2` is the normalized Hilbert--Schmidt length.

A **tensor replica** is a finite direct sum `Phi = (+)_k Phi_(i_k, j_k)^(+ m_k)` with
`Phi_(i,j)(g) = g^(tensor i) tensor conj(g)^(tensor j)` and `i + j >= 1`. It is a continuous homomorphism
`U(d) -> U(d')`, applied coordinatewise to tuples. So `w(Phi(U)) = Phi(w(U))` for every word `w`, and

```text
mu_(Phi(g)) = sum_k w_k  mu_g^(*i_k) * conj(mu_g)^(*j_k),    w_k proportional to m_k d^(i_k + j_k).   (R)
```

This class contains every amplification used in `classical-unitary-ratio-witnesses-amplify-to-metric-models`,
namely `U^(tensor k)` and `(U tensor conj U)^(tensor k)`.

## Statement

Fix `p in [1, infinity)` with `p != 2`. There are sequences `mu_m` (the data of the witnessed element `a(U)`) and
`nu_m` (the data of every relator `r(U)`) of conjugation-invariant probability measures on `T` such that the
following hold.

- **(i) Ratio witness.** `L_p(nu_m) / L_p(mu_m) -> 0`.
- **(ii) No constant-separation `p`-model.** For every `c in (0, 2]` there is an `m_0` with the following property.
  For every `m >= m_0` and every tensor replica `Phi`, if `L_p(Phi mu_m) >= c`, then `L_p(Phi nu_m) >= c/5`.
- **(iii) No classical comparison.** There is an `m_0` such that for `m >= m_0` and every tensor replica `Phi`,
  including the identity, each ratio below is at least `1/4`:

  ```text
  L_op(Phi nu_m)/L_op(Phi mu_m),    L_2(Phi nu_m)/L_2(Phi mu_m),    L_rk(Phi nu_m)/L_rk(Phi mu_m).
  ```

**The data.** Write `e(t) = (delta_(e^(it)) + delta_(e^(-it)))/2`.

- **(S>) For `p > 2`.** Take `mu = (1 - eta) delta_1 + eta delta_(-1)` and `nu = (1 - rho) e(eps) + rho delta_(-1)`.
  The parameters satisfy `eps <= 1`, `eps/pi` irrational, and

  ```text
  eps^p / eta -> 0,      rho / eta -> 0,      eta / eps^2 -> 0.
  ```

  For example `eta = 1/m`, `eps ~ m^(-1/p) / log m`, `rho = 1/(m log m)`.
- **(S<) For `1 <= p < 2`.** Take `mu = e(x)` and `nu = (1 - rho) e(y) + rho delta_(-1)`. The parameters satisfy
  `y <= x <= 1`, `y/pi` irrational, and

  ```text
  y / x -> 0,      rho / x^p -> 0,      x^2 / rho -> 0.
  ```

  For example `x = 1/m`, `y ~ x / log m`, `rho = y^p`.

In each case the three conditions are compatible exactly because `p != 2`. The last one would contradict the first
two at `p = 2`.

## The invariant and the death step

- **Invariant.** The pair of eigenvalue measures, which evolves by convolution (R) under every tensor replica.
- **Two growth laws under `n`-fold convolution.**
  - An atom of mass `eta` at a large angle spreads by **count**. It needs replica degree `n ~ 1/eta ~ L_p^(-p)` to
    reach constant length.
  - A symmetric spread of small angle `t` spreads by **variance**. It needs `n ~ t^(-2) ~ L_p^(-2)`.
- `L_p` weighs an angle `t` by `t^p`, so it balances the two laws only at `p = 2`.
- **Death step.**
  - For `p > 2`, the witnessed element is atomic and the relators are spread. The degree the element needs,
    `1/eta`, exceeds the degree at which the relators saturate, `1/eps^2`.
  - For `p < 2`, the witnessed element is spread and the relators carry rare atoms. The degree the element needs,
    `1/x^2`, exceeds the relator saturation degree `1/rho`.
- **Classical comparisons.** In both cases the relators keep an atom near `-1`, which blocks the operator
  comparison. They keep almost all their mass off `1`, which blocks the rank comparison. The mismatched scale
  blocks the HS comparison.

## Consequence (class kill)

- Consider any argument that turns a Schatten-`p` ratio witness into a metric model, for `p not in {2, infinity}`.
  Suppose it picks a tensor replica from the eigenvalue measures of `a(U)` and the `r(U)`, and certifies the
  outcome from the replicated eigenvalue measures alone.
- No such argument can prove any of the following from a `p`-ratio witness:
  - a constant-separation Schatten-`p` model;
  - an `l_op`, `l_2` or `l_rk` ratio witness, and hence MF, hyperlinearity or unitary rank approximability through
    `classical-unitary-ratio-witnesses-amplify-to-metric-models`.
- The reason is that (i)–(iii) give eigenvalue data that are consistent with the witness hypothesis and on which
  every such certificate fails.
- For `thompson-v-has-unbounded-compact-unitary-relator-width`, Schatten-`p` witnesses therefore remain an
  independent format. They are not reducible by the method that closed `op`, `HS` and `rank`.

**Not claimed.**
- That tuples realizing these data exist for the words of any presentation of `V`.
- That no other amplification works. Schur-functor replicas such as `Lambda^k` and `Sym^k`, compressions, and
  arguments that use the joint distribution of the words are untouched.
