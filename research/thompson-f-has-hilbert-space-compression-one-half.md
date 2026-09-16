---
rg: 2
id: thompson-f-has-hilbert-space-compression-one-half
kind: claim
title: Thompson's group F has Hilbert space compression 1/2
---

For a finitely generated group `G` with word metric `d`, the Hilbert space
compression `α(G)` is the supremum of the exponents `a ≥ 0` such that some
Lipschitz map `φ: G → H` into a Hilbert space satisfies

`‖φ(x) - φ(y)‖ ≥ C·d(x, y)^a - D` for all `x, y`, with constants `C, D > 0`.

This is equivalent to the Guentner–Kaminker form: the supremum, over
large-scale Lipschitz uniform embeddings `φ`, of
`liminf_{t→∞} log ρ_φ(t) / log t`, where
`ρ_φ(t) = inf{‖φ(x)-φ(y)‖ : d(x,y) ≥ t}`. The value does not depend on the
generating set.

**Claim.** `α(F) = 1/2`.

This is imported from Arzhantseva–Guba–Sapir (see the citation route). The route
that uses it, `thompson-t-compression-one-half-via-cylinder-charts`, needs only
`α(F) ≤ 1/2`.
