---
rg: 2
id: resolvent-steinberg-rf-residual-is-infinitely-normally-generated
kind: claim
title: For every prime l and N >= 3, the finite residual of St_N(R_l) contains infinitely many independent corner symbols, so it is not finitely normally generated
distinct_from:
  resolvent-steinberg-rf-residual-is-finitely-normally-generated: that is the open claim that the finite residual is finitely normally generated for some l and N >= 5; this is its negation.
  resolvent-elementary-groups-are-not-fp: that concerns E_N(R_l); this concerns the residually finite quotient of St_N(R_l), and needs in addition that the corner symbols die in every finite quotient.
artifacts:
  - research/artifacts/gq-gq-k2-q-resolvent-corner.md
---

**OPEN, with a complete proof modulo two classical inputs cited but not read at source (2026-09-18, lane
gq-k2-q).** Flip to ESTABLISHED after a referee confirms them:
- (DS) Dennis–Stein: `K_2(Z/l^r) = 0` for `l` odd, and `K_2(Z/2^r)` has order at most `2`. This is input (K-b)
  of `resolvent-steinberg-rf-residual-is-finitely-normally-generated`, recorded there from `gq-referee-b`.
- (vdK) van der Kallen: for a local ring, `K_2(N, ·) -> K_2(·)` is injective for `N >= 3`.

## Statement

For every prime `l` and `N >= 3`, the finite residual `K_rf` of `St_N(R_l)` is not the normal closure of a finite
set. Hence `resolvent-steinberg-rf-residual-is-finitely-normally-generated` fails, and the route
`z-localized-fp-rf-via-resolvent-steinberg-rf-quotient` is closed.

## Proof

1. **Finite quotients.** By `steinberg-rf-forces-ring-rf`, every finite quotient of `St_N(R_l)` factors through
   `St_N(F)` for a finite quotient ring `F` of `R_l`.
   - The corner map `Z_(l) -> e F e` has image a finite quotient of `Z_(l)`, that is `Z/l^r` or `0`.
   - So `c(λ,μ)` maps to the image of `{λ̄, μ̄}_N ∈ K_2(N, Z/l^r)`.
2. **Invisibility.** By (vdK) and (DS), `K_2(N, Z/l^r)` is `0` for `l` odd and has order at most `2` for `l = 2`,
   compatibly in `r`.
   - For odd `l`, every `c(λ,μ)` lies in `K_rf`.
   - For `l = 2`, the corner symbols killed by the limit map to `lim_r K_2(Z/2^r)`, a group of order at most `2`,
     form a subgroup of index at most `2`. It lies in `K_rf` and is still not finitely generated.
3. **Stable image.** Let `ι : St_N(R_l) -> St(R_l)`. Stable `K_2(R_l)` is central in `St(R_l)` (Kervaire), so
   `ι(g k g^(-1)) = ι(k)` for `k ∈ K_2(N, R_l)`. The normal closure of a finite set `{k_i} ⊂ K_rf` therefore has
   finitely generated image `⟨ι(k_i)⟩`.
4. **Conclusion.** `ι(K_rf)` contains the corner-symbol classes of step 2. By
   `resolvent-ring-corner-symbols-survive-in-k2` they are not finitely generated, so `K_rf` is not finitely
   normally generated. ∎
