---
rg: 2
id: mod-s2-separating-twist-characters-are-nontangent-at-one
kind: claim
title: Normalized separating-twist traces of exact Mod(S_2) representations approach 1 only inside a Stolz angle
distinct_from:
  mod-s2-exact-representations-have-a-torelli-scalar-gap: that asks omega to be absent from G_2; this asks only that G_2 be finite, which is the cone condition at 1, and says nothing about the prime three.
  mod-s2-separating-twist-circle-group-has-order-prime-to-three: that is the arithmetic half on the finite branch; this is the analytic half, excluding G_2 = S^1.
  mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap: that is the operator-norm gap; this is a local condition at 1 on the trace, i.e. on spectral variance versus mean, of near-identity images of t_s.
---

**OPEN.** In the notation of `mod-s2-separating-twist-character-semigroup-dichotomy`, there are `C > 0` and
`r_0 > 0` such that every finite-dimensional unitary representation `rho` of `Mod(S_2)` with
`|tr rho(t_s) - 1| < r_0` satisfies

```text
1 - |tr rho(t_s)|  >=  C |arg tr rho(t_s)| .
```

By (D5) this is equivalent to `G_2` being finite.

**Why it matters.** It is necessary for `mod-s2-exact-representations-have-a-torelli-scalar-gap`, since
`G_2 = S^1` contains `omega`. It is therefore also necessary for `deligne-central-mark-hs-collapse`. It
involves only near-identity representations: those with spectral variance of `rho(t_s)` small compared with
the spectral mean.

**How it can fail.** A family of honest representations in which `rho(t_s)` has spectrum concentrated near
`exp(i mu_n)`, with `mu_n -> 0`, `mu_n != 0` and variance `o(|mu_n|)`. By (D4) and (D6), tensor powers
`rho_n^(tensor k)` with `k ~ (2 pi/3)/mu_n` would then give `E_3` hyperlinear.

**Relation to the stability branch.**
- Suppose `Mod(S_2)` is matricially stable. The bus reports honest representations with `rho_n(t_s) -> 1` in
  operator norm and nonzero `Tr log rho_n(t_s)`; this has not been pinned in the graph.
- Under stability, this claim says those representations are *thick*: their variance is at least
  `C'|mean|`.

## Attempts
- **2026-09-18, swarm-0917-w12-w12-deligne-pull (probability-random): posed.** No test run.
  - Finite-image and SU(2) quantum representations have `rho(t_s)` of finite order. Its eigenvalues are roots
    of unity of bounded or growing order.
  - This bounds nothing uniformly, because averaging over many eigenvalues can produce small variance.
