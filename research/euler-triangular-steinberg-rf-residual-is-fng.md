---
rg: 2
id: euler-triangular-steinberg-rf-residual-is-fng
kind: claim
title: For some l and N >= 5, the finite residual of the finitely presented group St_N(T_l) is finitely normally generated
distinct_from:
  resolvent-steinberg-rf-residual-is-finitely-normally-generated: that is the same question for St_N(R_l), where the corner tame symbols of K_2(Z_(l)) are expected to refute it; this is over the triangular Euler ring T_l, which has no Z_(l) corner ring.
  euler-triangular-ring-has-fg-central-unstable-k2: that is a sufficient K-theoretic condition; this is the group-theoretic statement the bottleneck needs.
---

**OPEN.** There are a prime `l` and `N >= 5` such that the finite residual `K_rf` of `St_N(T_l)`, the
intersection of its finite-index normal subgroups, is the normal closure of a finite set.

**Use.** Then `Λ = St_N(T_l)/K_rf` is finitely presented, residually finite and contains `Z_(l)`, which is
`z-localized-embeds-in-fp-rf-group` (route `z-localized-fp-rf-via-euler-triangular-steinberg`).
- `K_rf ⊆ K_2(N, T_l)`, because `E_N(T_l)` is residually finite (`euler-base-embeds-in-fp-steinberg-group`).
- A sufficient condition is `euler-triangular-ring-has-fg-central-unstable-k2` (route
  `euler-triangular-residual-fng-from-fg-central-k2`).

## Attempts

None yet (2026-09-18, lane gq-infinite-primes).
