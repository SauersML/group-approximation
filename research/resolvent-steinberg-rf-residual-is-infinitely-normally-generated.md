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

**ESTABLISHED (2026-09-18)**, lane proof (gq-k2-q).
- `gq-referee-b` checked steps 1–4 given the two inputs below and found them correct
  (`research/artifacts/gq-referee-b-resolvent-ring-corner-symbols-survive-in-k2.md`).
- Both inputs were then read at the source by gq-k2-q (PDFs obtained through MSI, see the artifact):
  - **(DS)** R. K. Dennis and M. R. Stein, *The functor K_2: a survey of computations and problems*, LNM 342
    (1973), §12, pp. 254–255, verbatim: "if `W_m(F_q)` denotes the ring of Witt vectors of length `m` over `F_q`,
    `q = p^n`, then ... (ii) `K_2(W_m(F_q)) = 1` if `p` is odd or if `m = 1`; (iii) `K_2(W_m(F_q)) = Z/2Z` if
    `p = 2` and `m >= 2`." Here `W_m(F_p) = Z/p^m`.
  - **(vdK)** W. van der Kallen, *Injective stability for K_2*, LNM 551 (1976), Theorem 1, p. 77, verbatim: "Let `R`
    be a commutative ring with noetherian maximal spectrum of dimension `d`, `d < ∞`. Let `n >= d + 2`. Then the
    natural map `K_2(n,R) -> K_2(R)` is surjective and the natural map `K_2(n + 1,R) -> K_2(R)` is an
    isomorphism."
  - For `R = Z/l^r`, `d = 0`, so `K_2(N, Z/l^r) -> K_2(Z/l^r)` is an isomorphism for every `N >= 3`.
- Scope. Stability is applied only to the commutative local rings `Z/l^r`, never to the noncommutative `R_l`.
  The one fact used about `R_l` is that `K_2(R_l)` is central in `St(R_l)`, which holds for every ring (Milnor;
  quoted in the same survey, §1: "`K_2(R)` is precisely the center of the Steinberg group `St(R)`").

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
