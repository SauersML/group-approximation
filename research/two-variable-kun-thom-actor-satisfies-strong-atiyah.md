---
rg: 2
id: two-variable-kun-thom-actor-satisfies-strong-atiyah
kind: claim
title: The torsion-free two-variable Kun--Thom-type actor satisfies Strong Atiyah although it contains a Kazhdan group with two non-Ore compressors
distinct_from:
  char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup: that constructs the torsion-free finite-index subgroup for every number of variables d; this proves Strong Atiyah for it when d = 2, where the acting congruence group is free.
  one-compressor-support-atiyah-reduces-to-base: that shows a counterexample supported in a compression host needs two compressors with no common left multiple; this exhibits that pattern over an infinite Kazhdan group inside a torsion-free group satisfying Strong Atiyah, so the pattern alone forces nothing.
  double-ascending-hnn-strong-atiyah-reduces-to-kernel-tree: that reduces the free multiple ascending HNN extension to amalgams over compressed copies of the base; this is a quotient situation where the compressions satisfy extra relations and Strong Atiyah holds unconditionally.
---

**ESTABLISHED** by [[two-variable-kun-thom-actor-atiyah-proof]].

**Setting.** Let `r >= 2`, let `p >= 3` be prime, and let
`R = Z[x_1^(+-1), x_2^(+-1)]`. Put

```text
G_0 = EL_r(R) semidirect SL_2(Z),        alpha_A(x^v) = x^(A v)   (monomial substitution),
K   = ker( EL_r(R) -> GL_r(F_p) ),       evaluate at x = 1, then reduce mod p,
Gamma_2(p) = ker( SL_2(Z) -> SL_2(F_p) ),   H = K semidirect Gamma_2(p).
```

`H` is the torsion-free finite-index subgroup of
`char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup` for `d = 2`.

1. **Strong Atiyah.** `H` satisfies the Strong Atiyah conjecture over `C`. So
   `k[H]` is a domain for every field `k` of characteristic `0`.
2. **The compression pattern.** Let `r >= 3` and put
   `Gamma_0 = K cap EL_r(Z[x_1, x_2])`, the positive-polynomial part. Let

   ```text
   A_1 = [[1, p], [0, 1]],     A_2 = [[1, 0], [p, 1]]     in Gamma_2(p).
   ```

   Then:
   - `Gamma_0` is infinite and has property (T);
   - `A_i Gamma_0 A_i^-1` is a proper subgroup of `Gamma_0` for `i = 1, 2`;
   - `A_1, A_2` generate a free monoid, so positive words ending in different
     letters have no common left multiple.

## What it calibrates

* **The non-Ore shape is necessary, not sufficient.** The Attempts of
  `algebraic-strong-atiyah-counterexample-exists` and the node
  `one-compressor-support-atiyah-reduces-to-base` locate a counterexample over a
  compression host at supports using two compressors with no common left
  multiple over a Kazhdan group. That shape occurs here, in a torsion-free group
  satisfying Strong Atiyah over `C`.
* **Where it stops.**
  - In `H` the conjugates `A_1^-1 Gamma_0 A_1` and `A_2^-1 Gamma_0 A_2` satisfy
    extra relations: the Steinberg commutator relations of `EL_r(R)`. So the
    genuine amalgams of `double-ascending-hnn-strong-atiyah-reduces-to-kernel-tree`
    do not embed.
  - `H` is residually finite, since `G_0` is, hence sofic. This says nothing
    about nonsofic hosts.
* **Host status.** For `d = 2` the characteristic-zero actor is not a
  zero-divisor host in characteristic `0`. For `d >= 3` the quotient
  `Gamma_d(p)` has property (T), there is no locally indicable quotient, and
  Strong Atiyah for `K semidirect Gamma_d(p)` stays open. The Kun--Thom Theorem E
  pairs need `d >= 3`.

## Model test

* **Trivial model.** `p = 2` fails the hypothesis: `-I in Gamma_2(2)`, so `H`
  would contain an element of order two, and its averaging projection has trace
  `1/2`. Torsion-freeness of `CS(1,r,p)` and of `Gamma_2(p)` is exactly where
  `p >= 3` enters.
* **Real object.** `H` itself, with the explicit compressors above.
