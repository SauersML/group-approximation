---
rg: 2
id: one-sided-inverses-cannot-repair-the-steinberg-residual
kind: claim
title: The residually finite quotient St_N(T)/St_N(T)_rf depends only on T modulo its finite residual ideal, and residually finite rings are Dedekind-finite, so one-sided inverses of the lamps give the same group as two-sided ones
distinct_from:
  steinberg-rf-forces-ring-rf: that shows every finite quotient of St_N(R) factors through a finite quotient ring; this derives from it that the residually finite quotient group only sees R modulo its finite residual ideal.
  euler-ring-steinberg-rf-residual-is-fng: that is the open question for the Euler ring D; this shows that replacing the inverses of the lamps by one-sided inverses leaves that question unchanged.
  euler-base-annihilator-over-lamplighter-is-not-fg: that blocks imposing the Euler relation by finitely many module relations; this blocks weakening the ring relations to one-sided inverses.
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
  - research/artifacts/gq-referee-a-one-sided-inverses-cannot-repair-the-steinberg-residual.md
  - research/artifacts/gq-referee-b-one-sided-inverses-cannot-repair-the-steinberg-residual.md
---

**ESTABLISHED (2026-09-18)** through `one-sided-inverses-cannot-repair-the-steinberg-residual-proof`. Lane proof (gq-k2-q), elementary. *Reviewed:* PASS by
`gq-referee-a` (`research/artifacts/gq-referee-a-one-sided-inverses-cannot-repair-the-steinberg-residual.md`) and by
`gq-referee-b` (`research/artifacts/gq-referee-b-one-sided-inverses-cannot-repair-the-steinberg-residual.md`). The only
input is `steinberg-rf-forces-ring-rf` (refereed PASS).

## Statement

Let `T` be a unital ring and `N >= 3`. Write `I_rf(T)` for the intersection of the two-sided ideals of finite
index, and `Γ_N(T) = St_N(T)/St_N(T)_rf` for the largest residually finite quotient.

1. **Only the residually finite part of the ring matters.** For every two-sided ideal `I ⊆ I_rf(T)`:
   - `St_N(T)_rf` is the preimage of `St_N(T/I)_rf`;
   - so `Γ_N(T) ≅ Γ_N(T/I)`.

   If `I` is generated as a two-sided ideal by `g_1, …, g_s`, then the kernel of `St_N(T) -> St_N(T/I)` is the
   normal closure of the finitely many `x_ij(g_t)`.
2. **Dedekind-finiteness.** If `γπ = 1` in `T`, then `1 − πγ ∈ I_rf(T)`.
3. **One-sided inverses change nothing.** Suppose a design `T` has elements `γ_0, π_0` with `γ_0 π_0 = 1`, and the
   other lamps and their one-sided inverses are conjugates `π_k = x^k π_0 x^(-k)`, `γ_k = x^k γ_0 x^(-k)` by a unit
   `x`. (The same holds for right inverses, `π_0 γ_0 = 1`, with the ideal `(1 − γ_0 π_0)`.) Put
   `T' = T/(1 − π_0 γ_0)`, the quotient by the two-sided ideal. Then:
   - every `π_k` is a unit of `T'`;
   - `Γ_N(T) ≅ Γ_N(T')`.

   Moreover `St_N(T)_rf` is finitely normally generated if and only if `St_N(T')_rf` is, and a finite presentation
   of `T` gives one of `T'`. For the Euler lamps `π_k = u + 1 + kl`, `T'` again contains commuting units `π_k`, which is the situation of `euler-ring-steinberg-rf-residual-is-fng`. This is exact when `T` is the presentation of `D`
   with `π_0^(-1)` replaced by a one-sided inverse `γ_0`: then `T' ≅ D`.

## Scope

- Part 3 closes the one-sided-inverse repair for every design whose inverses propagate by conjugation from finitely
  many relators. It does not address:
  - inverses that act only on the corner `M`, through an annihilator relation such as `(βγ − 1)·M = 0`;
  - inverses supplied by non-commuting units.
- More generally, by Part 1 any repair may be assumed residually finite, since passing to `T/I_rf(T)` does not change
  `Γ_N`.
