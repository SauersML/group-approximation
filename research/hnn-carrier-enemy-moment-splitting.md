---
rg: 2
id: hnn-carrier-enemy-moment-splitting
kind: claim
title: Every carrier character over the regular character has pinned single-block moments and a tensor-split commutant
distinct_from:
  hnn-carrier-factorial-character-collapse: that is the open collapse claim (every factorial hyperlinear enemy centralizes the letter); this is an unconditional structure theorem valid for EVERY trace over the regular character, enemy or not, which pins all single-t-block moments and localizes the enemy's freedom in the two-block sector.
  hecke-averaging-realizes-commutant-expectation: that contracts a Lambda-central unitary onto its commutant expectation in a general tracial algebra; this applies it inside the GNS algebra of a carrier character and combines it with relative-icc moment identities special to the carrier.
  rcc-carrier-character-face-compression: that eliminates the ambient ultraproduct and reduces to factorial characters; this describes what those factorial characters must look like, shrinking the moduli the collapse claim has to kill.
---

Let `n` be odd (so `Z(SL_n(Z[1/p]))` is trivial; the downstream
instance is `n = 3`), `Gamma = SL_n(Z[1/p])`, `Lambda = SL_n(Z)`,
`H = < Gamma, t | [t, Lambda] = 1 >`, and let `tau` be ANY trace of
`H` with `tau|_Gamma = delta_e`.  Write `N = pi_tau(H)''`,
`k = pi_tau(t)`, `L(Gamma) = pi_tau(Gamma)''` (a factor, since
`Gamma` is ICC), and `Q = pi_tau(Gamma)' cap N`.  For even `n` every
statement below holds with the scalars replaced by the span of the
finite center.  Then:

1. **Single-block moments are pinned.**  For every `m != 0` and every
   `gamma in Gamma`,

   ```text
   E_(L(Gamma))(k^m) = tau(t^m) 1,
   tau(gamma t^m) = delta_e(gamma) tau(t^m).                    (MS1)
   ```

   In particular `tau` restricted to the subgroup
   `Lambda x <t> <= H` is the product `delta_e^Lambda otimes hat(mu)`
   where `mu` is the spectral measure of the unitary `k` on the
   circle (`hat(mu)(m) = tau(t^m)`), and every word of `H` containing
   exactly one block of `t`-letters has the trace forced by `mu`
   alone.

2. **The commutant tensor-splits.**  `Q` is `tau`-independent from
   `L(Gamma)`:

   ```text
   W*( L(Gamma) cup Q ) = L(Gamma) otimes-bar Q                 (MS2)
   ```

   with the product trace.  (In particular `Q` meets `L(Gamma)` in
   the scalars, and if `tau` is factorial with `Q = C` the lattice
   image is irreducible in `N`.)

3. **The commutant part of every power is a Hecke limit
   (`n >= 3`).**  Each `k^m` is a `Lambda`-central unitary of `N`, so
   `hecke-averaging-realizes-commutant-expectation` applies inside
   `N`: `E_Q(k^m) = lim_N S^N(k^m)` geometrically at rate
   `delta_0(n, p)`, and the leak scalar of `k^m` is
   `s_m = || E_Q(k^m) ||_2^2`.

4. **The enemy moduli live in the two-block sector.**  `tau` fails
   the collapse `(FC1)` iff `k notin Q`.  By 1 the values of `tau` on
   zero- and one-block words agree with those of the canonical HNN
   trace `delta_e^H` whenever `mu` is Haar measure (and are the
   `mu`-twist of them in general); the coefficient carrying the leak,
   `psi_k(gamma) = tau(t^(-1) gamma^(-1) t gamma)`, is a TWO-block
   word.  So the entire difference between an enemy and the canonical
   trace is concentrated in words with at least two `t`-blocks,
   parametrized by `mu` together with the multi-block moment data
   that the collapse claim must exclude.

Consequences.  The factorial reduction of
`rcc-carrier-character-face-compression` plus this splitting reduces
`hnn-carrier-factorial-character-collapse` to: no factorial
hyperlinear trace of `H` has two-block moments deviating from
`Gamma`-central ones while its one-block moments ride `(MS1)`.  For
the exact quasi-regular enemy of `no-exact-quasi-regular-leak`
(manufactured from a hyperlinear carrier), `mu` is Haar and the
two-block deviation is exactly `psi_k = 1_Lambda`, matching this
taxonomy.  The moment identities also show every enemy is
"generically placed": the letter is orthogonal not just to scalars
but to the whole lattice algebra in every power, `k^m - tau(k^m) 1
perp L^2(L(Gamma))`.
