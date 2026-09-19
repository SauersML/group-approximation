---
rg: 2
id: contracting-roots-need-winding-faster-than-contraction
kind: claim
title: In a contracting self-similar group an element whose carries along a good path stay bounded has roots of boundedly many orders prime to m!, and carries stay bounded whenever the orbit lengths grow no faster than the inverse contraction rate; so roots at infinitely many primes need an odometer that winds faster than the group contracts
distinct_from:
  contracting-groups-bound-roots-at-periodic-points: that kills generators with a good periodic point (bounded orbit lengths); this kills every generator with bounded carries, which includes that case and every odometer-like element winding no faster than the contraction rate, such as the standard odometer and its finite-state conjugates in any contracting group.
  z-localized-in-automaton-groups-needs-exotic-odometers: that uses rational points and finite-state orbit codings; this needs no rational point and no coding, only the finite nucleus and a length bound.
  separable-subgroups-are-z-semilocal-root-closed: that (bh-invent-12) is a profinite root-closure mechanism for separable subgroups; this is a geometric mechanism inside contracting groups, where cyclic subgroups need not be separable.
---

**ESTABLISHED** by `contracting-roots-need-winding-faster-than-contraction-proof` (lane bh-free-16, 2026-09-19;
elementary; not reviewed; no priority claimed). It does **not** settle contracting groups: fast-winding odometers
remain (item 4).

## Setting

Notation is as in `contracting-groups-bound-roots-at-periodic-points`.
- **The group.** `Γ <= Aut(T_m)` is self-similar and contracting, with nucleus `𝒩`. Fix a word metric `|·|` and
  constants `K >= 1`, `λ < 1`, `C` with `|g|_v| <= λ|g| + C` for all `g ∈ Γ` and `|v| = K`. Such constants exist
  for a suitable finite generating set (standard; see Nekrashevych, *Self-similar groups*, §2.11). Put `ρ_0 = λ^(1/K)`.
- **Orbits along a path.** Let `a ∈ Γ` have infinite order, and let `ξ` be a good path
  (`h_n = a^(c_n)|_(ξ_n)` of infinite order, where `c_n` is the length of the `a`-orbit of `ξ_n`).
- **Carries.** The *carries* of `a` at level `n` are the sections `A_j = a^j|_(ξ_n)`, `0 <= j <= c_n`. Note that
  `A_(c_n) = h_n`.
- **Admissible orders.** `k >= 2` is *`m`-free* if all its prime factors exceed `m`.

## Theorem

1. **Bounded carries bound the roots.** Suppose that for infinitely many `n` all carries `A_j` lie in one finite
   set `F`. Then at most `|F|^2 |𝒩|` `m`-free integers `k` have the property that `a` has a `k`-th root in `Γ`.
2. **Slow winding gives bounded carries.** `|A_j| <= M(ρ_0^n c_n |a| + C')` for constants `M, C'` that do not
   depend on `n` and `j`. So the carries are bounded along a subsequence as soon as
   ```
   liminf_(n→∞) c_n ρ_0^n < ∞.
   ```
   This covers:
   - bounded `c_n`, i.e. good periodic points (the earlier node);
   - the standard odometer, whose carries at `0^n` lie in `{1, a}` directly, so item 1 applies to it even
     without item 2;
   - every element whose orbit growth rate `limsup c_n^(1/n)` along some good path is below `1/ρ_0`.
3. **Consequence.** If `Z[1/P]` embeds in `Γ` with `1 ↦ a`, for an infinite set `P` of primes (for example
   `Z_(S)`), then along every good path the carries are unbounded, and `c_n ρ_0^n → ∞`. The generator must be an
   odometer that winds faster than `Γ` contracts, for every admissible choice of `(K, λ, C)`.
4. **Sharpness of the hypothesis.** In the contracting product odometer (`Z^2` translating `Z_3 × Z_2` on `T_6`),
   the element `a = (1,1)` has `c_n = 6^n`. Its carries `A_j = (⌊j/3^n⌋, ⌊j/2^n⌋)` are unbounded, since `ρ_0 = 1/2`
   there. So fast winding with unbounded carries really occurs in contracting groups. This element still has no
   roots.

## What is left for contracting groups

A contracting witness for (SL), or for `Q ⋊ ⟨2⟩` through `natural-q-rtimes-2-in-2v-h-iff-odd-odometer-roots`, needs
a generator `a` with all of the following:
- `a` is not a translation;
- `a` has no good periodic point;
- `a` has unbounded carries along every good path, which forces `c_n ρ_0^n → ∞`;
- `a` has infinite-state orbit codings.

The one remaining argument to find is a bound on the roots' sections in terms of the carries' *fractional* part.
In the product odometer the carries run along the line from `1` to `h_n` (`A_j ≈ h_n^(j/c_n)` up to bounded error).
There the root would need a section with denominator `k`, which the finite nucleus cannot supply for infinitely
many `k`. Whether every fast-winding odometer in a contracting group has carries that are "bounded modulo a
one-parameter family" in this sense is open.

## Lesson for general BH

**Roots cost a torsion-free pair in the nucleus, paid at the first level where the carries are bounded.**
- A `k`-th root `r` of `a` shifts the `a`-orbit of `ξ_n` by `d ≡ k^-1`, and `a^-d r` returns to `ξ_n`.
- Its section `γ` there satisfies `γ^k = h_n^e`, with `gcd(e, k) = 1`. If carries are bounded, `γ` lies in the
  finite set `F^-1 𝒩`, and `(h_n, γ)` determines `k`.
- So a finite nucleus gives a finite prime budget unless the element winds faster than the group contracts.
- Divisibility in self-similar groups therefore needs one of three things: infinite-state generators (no nucleus);
  fast-winding odometers whose carries leave every ball; or non-contracting dynamics.

This is the same carrier principle as before, stated as a winding-versus-contraction inequality: the
arithmetic of the input must be paid for by growth that local contraction cannot absorb.
