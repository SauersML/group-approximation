---
rg: 2
id: fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff-proof
kind: route
title: Push the subcritical susceptibility bound to p_c by Fekete and lower semicontinuity, then thin a short open path at a critical worst pair
target: fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff
requires:
  - fpbs-worst-pair-connectivity-rate-kernel
  - fpbs-intrinsic-rates-log-lipschitz-in-parameter
  - fpbs-intrinsic-l2-rate-closed-zero-set
---

Complete written proof. Notation as in the claim. No computation is used.

**Inputs.**

- **(I1)** Item 1 of `fpbs-worst-pair-connectivity-rate-kernel`: supermultiplicativity
  `kappa_p(n+m) >= kappa_p(n) kappa_p(m)` (Harris-FKG along a geodesic), the
  limit `gamma(p) = inf_n -(1/n) log kappa_p(n)`, and lower semicontinuity of
  `p -> tau_p(o,v)` (a supremum of polynomials). Item 2 of the same claim:
  uniqueness at `t` gives `tau_t(u,v) >= theta(t)^2`, where
  `theta(t) = P_t(o <-> infinity)`.
- **(I2)** Item 1 of `fpbs-intrinsic-rates-log-lipschitz-in-parameter`
  (thinning): for `0 < p <= t <= 1` and `R >= 1`,
  `P_t(d_omega(u,v) <= R) <= (t/p)^R P_p(d_omega(u,v) <= R)`.
- **(I3)** Fact (F4) as isolated in
  `fpbs-intrinsic-rates-log-lipschitz-in-parameter-proof`, from Lemma 3.1 of
  `fpbs-intrinsic-l2-rate-closed-zero-set-proof` with the Duminil-Copin--Tassion
  import: `chi(p) = E_p|C_o| < infinity` for every `p < p_c`.
  (I3) does not use the unsupported closedness sentence of that proof.
- **(I4)** Ball growth: `|B_(n+m)| <= |B_n| |B_m|`, since every word of length
  at most `n+m` is a product of words of lengths at most `n` and `m`. Fekete
  then gives `gr = inf_n |B_n|^(1/n)`, so `|B_n| >= gr^n`.

## Item 1

Fix `0 < p < p_c` and `n >= 1`. By transitivity and (I3),

```text
|B_n| kappa_p(n)  <=  sum_(v in B_n) tau_p(o,v)  <=  E_p|C_o|  =  chi(p) < infinity .
```

By (I4), `kappa_p(m) <= chi(p) gr^(-m)` for every `m`. By (I1),
`kappa_p(kn) >= kappa_p(n)^k` for every `k >= 1`, so

```text
kappa_p(n)  <=  kappa_p(kn)^(1/k)  <=  chi(p)^(1/k) gr^(-n)   -->   gr^(-n)   (k -> infinity).
```

So `kappa_p(n) <= gr^(-n)` for every `p < p_c`.

For `p = p_c`: `B_n` is finite, so pick `p_j ↑ p_c` and `v in B_n` with
`tau_(p_j)(o,v) = kappa_(p_j)(n) <= gr^(-n)` for every `j`. Some `v` is the
minimiser for infinitely many `j`; pass to that subsequence. By lower
semicontinuity (I1), `tau_(p_c)(o,v) <= liminf_j tau_(p_j)(o,v) <= gr^(-n)`.
So `kappa_(p_c)(n) <= gr^(-n)` for every `n`. Taking logarithms and
`n -> infinity` gives `gamma(p_c) >= log gr`.

## Item 2

Fix `t in (p_c,1]`. If `l(t) = infinity` there is nothing to prove.

*Upward closure.* `s_t(v,R)` is nondecreasing in `R` and at most `1`. So the
set of admissible `L` in the definition of `l(t)` is upward closed, and every
`L > l(t)` is admissible.

Fix `L > l(t)` and `eta > 0`. Since `L` is admissible, there are infinitely
many `n` and points `v_n in A_n` with `s_t(v_n, Ln) >= e^(-eta n)`.

*No trivial pairs.* `v_n != o`, because
`tau_(p_c)(o,v_n) = kappa_(p_c)(n) <= gr^(-n) < 1` by item 1. So
`s_t(v_n, R) = 0` for `R < 1`, and `R_n := floor(Ln) >= 1`.

*Chain of bounds.* Using the definition of `s_t`, then (I2) with
`p = p_c`, then `{d_omega(o,v) <= R} ⊆ {o <-> v}`, then (I1):

```text
tau_t(o,v_n)  =  P_t(d_omega(o,v_n) <= R_n) / s_t(v_n,R_n)
             <=  e^(eta n) (t/p_c)^(R_n) P_(p_c)(d_omega(o,v_n) <= R_n)
             <=  e^(eta n) (t/p_c)^(L n) tau_(p_c)(o,v_n)
              =  e^(eta n) (t/p_c)^(L n) kappa_(p_c)(n)
             <=  e^(eta n) (t/p_c)^(L n) e^(-gamma(p_c) n) .
```

The last line uses `gamma(p_c) = inf_m -(1/m) log kappa_(p_c)(m)`.

*Passing to the limit.* Since `v_n in B_n`, `kappa_t(n) <= tau_t(o,v_n)`. So
along infinitely many `n`,

```text
-(1/n) log kappa_t(n)  >=  gamma(p_c) - L log(t/p_c) - eta .
```

The left side converges to `gamma(t)` by (I1), so `gamma(t)` obeys the same
bound. Letting `eta -> 0` and `L ↓ l(t)` gives
`gamma(t) >= gamma(p_c) - l(t) log(t/p_c)`. Item 1 gives the second
inequality.

## Item 3

By item 2, `gamma(t) >= log gr - l(t) log(t/p_c) > 0` with `t > p_c`. That is
kernel (K), and item 4 of `fpbs-worst-pair-connectivity-rate-kernel` gives
`p_c < p_u`.

## Item 4

*Uniqueness kills gamma.* `t > p_c` gives `theta(t) > 0`. Uniqueness and (I1)
give `kappa_t(n) >= theta(t)^2` for all `n`, so `gamma(t) = 0`.

*The forced slope.* Item 2 then gives `l(t) log(t/p_c) >= log gr > 0`. So
`l(t) >= log(gr)/log(t/p_c)`, and, when `l(t) < infinity`,
`t >= p_c gr^(1/l(t))`.

*Collapse.* Suppose `p_c = p_u`. Every `t > p_c` exceeds `p_u`, so `omega_t`
has a unique infinite cluster a.s. This uses monotonicity of uniqueness
(Häggström–Peres, Schonmann), the same convention as item 4 of
`fpbs-worst-pair-connectivity-rate-kernel`. With `t = p_c + epsilon` and
`log(1+x) <= x`,

```text
l(p_c + epsilon)  >=  log(gr) / log(1 + epsilon/p_c)  >=  p_c log(gr) / epsilon .
```

## Item 5

Let `K` be a linear stretch constant at `t > p_c`, so that
`c := inf_(u,v) P_t(d_omega(u,v) <= K(d(u,v)+1)) > 0`.

Take `v_n in A_n`. Then `d(o,v_n) <= n`. Put `R_n = floor(K(n+1))`, which is
at least `1` for large `n`. By (I2) and item 1,

```text
c  <=  P_t(d_omega(o,v_n) <= R_n)  <=  (t/p_c)^(K(n+1)) tau_(p_c)(o,v_n)  <=  (t/p_c)^(K(n+1)) gr^(-n) .
```

Take logarithms, divide by `n`, and let `n -> infinity`. This gives
`0 <= K log(t/p_c) - log gr`.

## Item 6

`T_d` is the Cayley graph of the free product of `d` copies of `Z/2`. It has
`gr = d-1` and `p_c = 1/(d-1)`. The unique simple path gives
`tau_p(o,v) = p^|v|`, so the minimisers of `tau_(p_c)(o,.)` on `B_n` are
`A_n = S_n`. Also `kappa_p(n) = p^n` and `gamma(p) = -log p`.

On `{o <-> v}`, the only open path is the geodesic, so
`d_omega(o,v) = |v| = n` for `v in S_n`. Hence:

- `s_t(v,Ln) = 1` for `L >= 1`;
- `s_t(v,Ln) = 0` for `L < 1`;
- `l(t) = 1`.

Then

```text
gamma(t) + l(t) log(t/p_c)  =  -log t + log(t(d-1))  =  log(d-1)  =  gamma(p_c)  =  log gr .
```
