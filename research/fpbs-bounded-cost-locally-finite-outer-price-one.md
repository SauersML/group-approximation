---
rg: 2
id: fpbs-bounded-cost-locally-finite-outer-price-one
kind: claim
title: A bounded-cost normal subgroup with infinite locally finite quotient acting almost faithfully by outer automorphisms forces fixed price one
distinct_from:
  fpbs-normal-subgroup-bounded-cost-fixed-price-one: that allows any infinite quotient; this is its special case with an infinite locally finite quotient whose outer action on the normal subgroup has finite kernel.
  fpbs-bounded-cost-outer-cyclic-extension-price-one: that is the case of quotient Z; this is the torsion case in which every finitely generated subgroup of the quotient is finite.
  fpbs-bounded-cost-fg-torsion-quotient-price-one: that is the torsion case with a finitely generated infinite quotient; this is the locally finite case, where no finitely generated subgroup is infinite.
  fpbs-amenable-outer-kernel-forces-price-one: that established lemma settles locally finite quotients with infinite outer kernel; this assumes a finite outer kernel, so the lemma does not decide it, and the cost bound must be used.
artifacts:
  - research/artifacts/fpbs-normal-bounded-cost-quotient-trichotomy-2026-09-16.md
---

**OPEN.** Let `N` be an infinite normal subgroup of a countable group
`Gamma`. Suppose every essentially free p.m.p. action of `N` has cost at most
some `K < infinity`. Suppose `Gamma/N` is infinite and locally finite, and the
outer action `Gamma/N -> Out(N)` has finite kernel. Then `Gamma` has fixed
price one.

**Scope.**
- This is case (b) of `fpbs-bounded-cost-normal-via-quotient-trichotomy`.
- **The infinite-kernel case is established.** By
  `fpbs-amenable-outer-kernel-forces-price-one`, the statement holds without
  any cost bound when the kernel is infinite.
- **Vacuous cases.** Suppose every locally finite subgroup of `Out(N)` is
  finite, for example when `Out(N)` is virtually torsion-free. Then the image
  of `Gamma/N` is finite, so the kernel is infinite and the hypothesis never
  holds.

## Attempts

* **Exhaust by finite extensions.**
  - Write `Gamma/N` as an increasing union of finite groups `Q_n`, and let
    `Gamma_n` be the preimages.
  - Absorbing each group element on a small complete section of `R_N` gives
    `C(Gamma↷X) <= inf_n C(Gamma_n↷X)`.
  - The coset extension satisfies
    `C(Gamma_n↷X x Gamma_n/N) = 1 + (C(N↷X)-1)/|Q_n|`, which tends to one.
  - **Where it dies:** returning from the coset extension to `X` is the open
    equality direction of `fpbs-finite-fiber-cost-bound`. The available bound
    `C(X) <= 1 + |Q_n|(C(Y)-1)` gives back only `C(N↷X) <= K`.
  - Pseudocost exhaustion likewise gives only `PC <= K`.
* **Ergodic decomposition of `R_N`.**
  - `Gamma/N` acts on the space of `N`-ergodic components.
  - If this action is free, Theorem A of the normal-subgroup note gives cost
    one, since every free action of the amenable quotient has cost one.
  - **Where it dies:** in the Bernoulli shift the component space is a point
    and the stabilizer is the whole quotient. Non-free invariant random
    subgroups of the quotient are not handled.
