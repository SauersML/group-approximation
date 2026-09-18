---
rg: 2
id: one-sided-inverses-cannot-repair-the-steinberg-residual
kind: claim
title: The residually finite quotient St_N(T)/St_N(T)_rf depends only on T modulo its finite residual ideal, and residually finite rings are Dedekind-finite, so one-sided inverses of the lamps give the same group as two-sided ones
distinct_from:
  steinberg-rf-forces-ring-rf: that shows every finite quotient of St_N(R) factors through a finite quotient ring; this derives from it that the residually finite quotient group only sees R modulo its finite residual ideal.
  euler-ring-steinberg-rf-residual-is-fng: that is the open question for the Euler ring D; this shows that replacing the inverses of the lamps by one-sided inverses leaves that question unchanged.
  euler-base-annihilator-over-lamplighter-is-not-fg: that blocks imposing the Euler relation by finitely many module relations; this blocks weakening the ring relations to one-sided inverses.
requires:
  - steinberg-rf-forces-ring-rf
artifacts:
  - research/artifacts/gq-gq-k2-q-rf-hosts.md
---

**ESTABLISHED (2026-09-18)**, proof below. Lane proof (gq-k2-q), elementary, not independently reviewed. The only
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
   of `T` gives one of `T'`. For the Euler lamps `π_k = u + 1 + kl`, `T'` again contains commuting units `π_k`, which is the situation of `euler-ring-steinberg-rf-residual-is-fng`.

## Proof

**Part 1.**
- By `steinberg-rf-forces-ring-rf`, every homomorphism of `St_N(T)` onto a finite group factors through
  `St_N(F)` for a finite quotient ring `F = T/J`. Since `J` has finite index, `J ⊇ I_rf(T) ⊇ I`.
- So the finite quotients of `St_N(T)` and of `St_N(T/I)` correspond under the surjection
  `St_N(T) -> St_N(T/I)`, and `St_N(T)_rf` is the preimage of `St_N(T/I)_rf`. The isomorphism of the quotients
  follows.
- *The kernel.* `St_N(T/I)` is `St_N(T)` with the extra relations `x_ij(a) = 1` for `a ∈ I`: both have generators
  `x_ij(r)` subject to the Steinberg relations, and in the quotient `x_ij(r)` depends only on `r mod I`.
  - For `a = Σ t g_t t'`, use additivity of `x_ij`.
  - Pick `k ∉ {i, j}`, which exists since `N >= 3`. Then `x_ij(t g t') = [x_ik(t), x_kj(g t')]` and
    `x_kj(g t') = [x_ki(g), x_ij(t')]`.
  - So every `x_ij(a)` lies in the normal closure of the `x_ij(g_t)`. ∎

**Part 2.** Let `F` be a finite quotient ring. Left multiplication by `π̄` is injective, since `γ̄π̄ f = f`. `F` is
finite, so it is bijective, and `π̄ g = 1` for some `g`. Then `γ̄ = γ̄(π̄ g) = g`, so `π̄ γ̄ = 1`. Hence
`1 − πγ` lies in every finite-index two-sided ideal. ∎

**Part 3.**
- `x^k (1 − π_0 γ_0) x^(-k) = 1 − π_k γ_k`, so the ideal `I = (1 − π_0 γ_0)` contains every `1 − π_k γ_k`. In `T'`,
  `γ_k` is then a two-sided inverse of `π_k`.
- `I ⊆ I_rf(T)` by Part 2, so `Γ_N(T) ≅ Γ_N(T')` by Part 1.
- By Part 1, `St_N(T)_rf` is the preimage of `St_N(T')_rf` under a surjection whose kernel is the normal closure
  of the finitely many `x_ij(1 − π_0 γ_0)`. A preimage of a finitely normally generated normal subgroup under such
  a map is finitely normally generated, and so is an image. `T'` has one more relation than `T`. ∎

## Scope

- Part 3 closes the one-sided-inverse repair for every design whose inverses propagate by conjugation from finitely
  many relators. It does not address:
  - inverses that act only on the corner `M`, through an annihilator relation such as `(βγ − 1)·M = 0`;
  - inverses supplied by non-commuting units.
- More generally, by Part 1 any repair may be assumed residually finite, since passing to `T/I_rf(T)` does not change
  `Γ_N`.
