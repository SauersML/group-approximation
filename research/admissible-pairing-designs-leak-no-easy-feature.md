---
rg: 2
id: admissible-pairing-designs-leak-no-easy-feature
kind: claim
title: On admissible pairing designs every decodable matching feature leaves a hard split game, so test transparency is exhausted there
distinct_from:
  noise-test-transparent-on-decodable-matching-features: that lower-bounds the test by any decodable split game on every instance; this combines it with the admissible-design soundness transfer to show no admissible design can leak an easy feature.
  random-exponential-pairing-families-are-unlearnable: that shows random exponential families defeat member list decoders; this covers every admissible design, random or structured, and every decodable feature.
---

**ESTABLISHED.** Let `F` be a pairing design that is `(8d+1)`-wise uniform and
`(K,m,C_0)`-smooth, with the parameters BKM's Section 5 fixes for output
soundness `epsilon` (`noise-test-sound-on-smooth-design-rich-inputs`). Take
`n >= n_0`, and let `Psi` be a regular 2-to-1 game whose pairing family at
every left vertex is admissible and whose value is at most `eta`. Then, for
every shift-invariant decodable feature `c` with decoder error `e_c`,

```text
val(Psi_c) <= sqrt( (epsilon + 2 e_c) / ((1-1/m) rho^3) ).
```

**Regime.** Fix `epsilon`. BKM's Section 5 then fixes `m >= m_0(epsilon)`,
`rho = 1-epsilon`, `K`, `d` and the strength `t = 8d+1`, and the transfer is a
large-`n` statement (`n >= n_0`). The bound drops the `-1/m` term from
`epsilon - 1/m + 2 e_c`. That is simply a weakening, so it needs no assumption
about `1/m` versus `epsilon`.

**Barrier exhausted.** Feature transparency certifies unsoundness and nothing
else, and the test is sound on admissible designs. So no admissible design,
random or structured, can leak a decodable feature with an easy split game on a
low-value instance. Leaks are possible only on non-admissible designs: too
little strength, or no bounded smoothness constant.

**What an outer PCP must provide.** Exactly
`smooth-design-rich-2to1-hardness`: NP-hardness of `Gap-2-to-1[1-eta, eta]` on
instances whose pairing family at every left vertex is `(8d+1)`-wise uniform
and smooth at the `(m,K)` the reduction uses. That forces at least about
`m^n/C_0` distinct matchings per left vertex
(`pullback-smoothness-needs-exponentially-many-pairings`). No separate
feature-safety requirement needs checking.

**Consistency test for proposals.** If a construction has a decodable feature
whose split game is easy in the NO case, then it is not admissible, or it is not
sound as a 2-to-1 game. For example, an enrichment of the Grassmann 2-to-1
instances that keeps the affine direction recoverable must make the
direction-split game hard to approximate, or it fails one of the two
properties.

This is conditional on the soundness transfer, which carries over BKM's
published analytic proof. No hardness or status of UGC is asserted.

DERIVATION admissible-designs-feature-safety-proof
