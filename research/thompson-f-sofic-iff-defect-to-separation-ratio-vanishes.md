---
rg: 2
id: thompson-f-sofic-iff-defect-to-separation-ratio-vanishes
kind: claim
title: Thompson's F is sofic exactly when relator defect can be made arbitrarily small relative to commutator separation, so nonsoficity is one linear inequality
distinct_from:
  thompson-f-sofic-iff-relator-system-unstable: that makes soficity equivalent to almost-solutions whose defect tends to 0 while separation stays bounded below; this shows that the ratio of defect to separation tending to 0 already suffices, at any sizes, and turns nonsoficity into a linear inequality with one constant.
  thompson-f-relator-system-stable-in-permutations: that is the qualitative stability question; this shows that an affirmative answer is automatically linear in the separation form.
  thompson-f-spatial-permutation-models-almost-commute: that bounds separation by the following error of models over the interval; this compares separation with relator defect, the quantity that coordinatewise powers carry.
artifacts:
  - research/artifacts/hl-f-sofic-relator-instability-2026-09-14.md
---

**ESTABLISHED (unreviewed).** **Setting.**
- `F = <a, b | R_1, R_2>` with `R_1 = [ab^-1, a^-1ba]` and `R_2 = [ab^-1, a^-2ba^2]`, and `d` is
  the normalized Hamming distance.
- For `A, B ∈ Sym(n)`: the *separation* is `t(A,B) = d(AB, BA)`, the *defect* is
  `D(A,B) = max_j d(R_j(A,B), 1)`, and `D_+(A,B) = d(R_1(A,B),1) + d(R_2(A,B),1)`.
- `ρ_F = inf { D(A,B)/t(A,B) : n ≥ 1, A, B ∈ Sym(n), t(A,B) > 0 }`. Exact solutions commute, so
  `D = 0` forces `t = 0`.

**Statement.**
1. **Criterion.** `F` is sofic exactly when `ρ_F = 0`.
2. **Linear form.** `F` is not sofic exactly when some `C < ∞` has
   `d(AB, BA) ≤ C · max_j d(R_j(A,B), 1)` for all `n` and all `A, B ∈ Sym(n)`. The best constant is
   `1/ρ_F`. The same holds with `D_+`, since `D ≤ D_+ ≤ 2D`.
3. **Explicit amplification.** If `t(A,B) = t > 0` and `D(A,B) = ρt`, then for every `K > 0` the
   coordinatewise power `(A^(×m), B^(×m))` on `[n]^m`, with `m = ⌈K/t⌉`, has separation at least
   `1 - e^-K` and defect at most `(K+1)ρ`.
4. **Unions and products don't lower the ratio.** For `r ∈ (0,1]`, the pairs with `D_+ ≥ r·t` form a
   class closed under disjoint unions and coordinatewise products.
5. **One number fixes the envelope.** Let `E(τ) = inf { D(A,B) : n ≥ 1, A, B ∈ Sym(n), t(A,B) ≥ τ }`.
   For every `τ ∈ (0,1)`,

   `ρ_F · τ ≤ E(τ) ≤ ρ_F · (1 + ln(1/(1-τ)))`.

   So the least defect needed for separation `τ` is `ρ_F` times `τ`, up to a logarithmic factor.

**Consequences.**
- **A witness needs only a vanishing ratio.** Any family with `D/t → 0` proves `F` sofic, whatever
  the sizes, defects and separations. For instance separation of order `defect^α` with `α < 1` would do.
  Neither the defect nor the following error has to tend to 0.
- **Nonsoficity is one inequality.** Every proof that `F` is not sofic proves the linear bound of item
  2. The stable form of Arzhantseva--Păunescu's Open problem is equivalent to it.
- **Mixing blocks is no route.** Disjoint unions, coordinatewise products and commuting torus factors of
  blocks with `D_+ ≥ r·t`, `r ≤ 1`, never go below `r`. In the landed exact profiles,
  `x_0`-ray windows and truncations have `D_+/t ≈ 2` and perturbed commuting pairs `≈ 4`, so every
  mixture of them keeps `D_+ ≥ t`.
- **Small blocks do better, and decide nothing.** Exact enumeration over `Sym(n)` for `n ≤ 12` gives
  minimum `max(m_1,m_2)/m_c = 1/3` at `n = 12` and minimum `(m_1+m_2)/m_c = 1/2` from `n = 10` on. Here
  `m_1, m_2, m_c` count the points moved by `R_1`, `R_2` and the commutator. The certificate pairs
  are in the artifact. So `ρ_F ≤ 1/3`, and any constant in item 2 is at least 3. This says nothing
  about whether `ρ_F = 0`.

**Scope.** Elementary. The amplification is the coordinatewise-power step of the landed Lemma 2.2, with
numbers attached, and no novelty is claimed for the principle. It decides nothing about
`thompson-f-is-sofic`.

Proof route: `thompson-f-sofic-iff-defect-to-separation-ratio-vanishes-proof`.
