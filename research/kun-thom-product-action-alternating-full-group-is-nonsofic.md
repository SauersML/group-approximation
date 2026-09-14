---
rg: 2
id: kun-thom-product-action-alternating-full-group-is-nonsofic
kind: claim
title: The alternating full group of a Kun--Thom wreath acting on lamp configurations times a finite quotient is nonsofic
distinct_from:
  kun-thom-nonsofic-wreath: that is nonsoficity of the wreath itself; this places a finite-index subgroup of the wreath's image inside Nekrashevych's alternating full group of a product action, with no equality between the alternating and commutator full groups.
  permanence-closure-contains-fg-simple-nonsofic-group: that asks for a finitely generated simple nonsofic group in the permanence closure; this settles only the nonsofic part, for the corrected candidate.
artifacts:
  - research/artifacts/kun-thom-alternating-full-group-2026-09-12.md
---

**ESTABLISHED** by `kun-thom-product-action-alternating-full-group-nonsofic-proof`.

**Setting.**
- `(G, Gamma)` is the pair of Kun--Thom Theorem E, and `W = (Z/2) wr_(G/Gamma) G = N semidirect G`.
- `K` is a normal subgroup of finite index in `G` with `|G/K| >= 3`.
- `W` acts on `Y = {0,1}^(G/Gamma) x G/K` by `(n,g).(x,p) = (n + g.x, g p)`.
- `A(Y)` is Nekrashevych's alternating full group of this action.

**Theorem.** `A(Y)` contains the image of `N semidirect [K,K]`, a finite-index subgroup of the image of `W`. So
`A(Y)` is nonsofic.

**On lamp configurations alone.** `A({0,1}^(G/Gamma))` contains the image of `N semidirect EL_r(R)`. It contains the
image of `[W,W]` exactly when it contains the image of `SL_d(Z)`, which is open. An element whose image in `SL_d(Z)`
has infinite order preserves no proper clopen set, so fragmentation cannot place it.

Proof: Sections 1--3 of the linked artifact.
