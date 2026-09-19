---
rg: 2
id: scale-periodic-bs-chain-germ-representations-are-not-faithful
kind: claim
title: Every piecewise-linear germ realization of the Baumslag-Solitar chain at an end of the line (translation, doubling, and any dyadic PL germ conjugating doubling to quadrupling) kills a nontrivial element of the chain group, so the germ group is a proper quotient of it
distinct_from:
  bs-chain-configurations-exist-in-finite-germ-extensions-of-v: that exhibits one realization and records that the whole question moves to the germ group at +∞; this shows the germ group is never the chain group itself for any PL choice of the square map, so its finite presentation cannot be inherited from the chain group.
  normal-germ-extensions-of-thompson-v-contain-no-sl3z: that (Lemma 5) shows germ groups in which the zoom is normal carry no Baumslag-Solitar dilation at all; this is about the complementary regime, where the zoom sits at the bottom of the tower, and finds relations there instead.
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no priority claimed).

## Setting

Germs at `+∞` of homeomorphisms of the half-line `(X, ∞)`. These are the germs of the finite germ
extensions of `V` on the Cantorized line of `bs-chain-configurations-exist-in-finite-germ-extensions-of-v`,
read in real coordinates.
- `σ(x) = x + 1`, the `V`-zoom at `+∞`.
- `δ(x) = 2x`.
- `s` is any germ that is dyadic PL with discrete breakpoints and satisfies `s δ s^-1 = δ^2`, that is
  `s(2x) = 4 s(x)` for large `x`. The odd dyadic square map `a` of the source node is one choice.

Let `G_1 = ⟨s, δ, σ | s δ s^-1 = δ^2, δ σ δ^-1 = σ^2⟩ = BS(s,δ) *_⟨δ⟩ BS(δ,σ)`. It is the chain group of
`higman-chain-group-pbh-iff-chain-configuration`, written in the convention of the germ node. Let
`θ : G_1 -> Q = ⟨σ, δ, s⟩` be the germ representation.

## Statement

Put `τ = s^-1 σ s` and `c_1 = [τ, σ] = τ σ τ^-1 σ^-1`. For every such `s` there is `k_0` such that, for all
`k >= k_0`, the element `w_k = [c_1, σ^k c_1 σ^-k]` satisfies:
1. `θ(w_k) = 1`;
2. `w_k ≠ 1` in `G_1` (this holds for every `k >= 2`).

So `ker θ ≠ 1`, and `Q` is a proper quotient of `G_1`. The chain configuration survives, since `σ` has
infinite order in `Q`.

## Proof

- **Breakpoints of s are sparse.** `s(2x) = 4 s(x)` gives `s'(2x) = 2 s'(x)`. So `s` restricted to
  `[2^j X, 2^(j+1) X)` is the rescaled copy of `s` on `[X, 2X)`. It has the same number `N >= 1` of
  breakpoints, and on that interval `s' >= 2^j m_0`, where `m_0 > 0` is the least slope on `[X, 2X)`.
  (`N = 0` is impossible: an affine `s` gives `s(2x) = 2 s(x) + const`.) So consecutive breakpoints
  `β < β'` at scale `j` satisfy `β' - β >= 2^j g_0` for a fixed `g_0 > 0`.
- **τ is a translation off the breakpoints.** `τ(x) = s^-1(s(x) + 1)`. If `x` and `τ(x)` lie in one
  piece of `s` then `τ` is the translation by `1/s'(x) <= 2^-j/m_0` near `x`. Otherwise `x` lies within
  `1/s'` of a breakpoint. So `τ` is a local translation outside `U = ⋃_β [β - 1, β + 1]` (for large
  scales), and so are `τ^-1` and `σ^±1`.
- **c_1 has sparse support.** `c_1(x) ≠ x` forces one of `x`, `σ^-1 x`, `τ^-1 σ^-1 x` or
  `σ τ^-1 σ^-1 x` into `U`. So `supp c_1 ⊆ ⋃_β [β - 3, β + 3]` at large scales. Then
  `supp(σ^k c_1 σ^-k) ⊆ ⋃_β [β + k - 3, β + k + 3]`.
- **Disjoint supports commute.** For `k >= 7`, and at scales where `2^j g_0 > k + 6`, the two supports
  are disjoint. So the two germs commute and `θ(w_k) = 1`.
- **w_k ≠ 1 in G_1.** Write `A = BS(s,δ)`, `B = BS(δ,σ)` and `C = ⟨δ⟩`. The letters `s^±1` lie in
  `A \ C`, and `σ^m` lies in `B \ C` for `m ≠ 0`. `c_1 = s^-1 σ s σ s^-1 σ^-1 s σ^-1` is alternating.
  Expanding `w_k = c_1 · σ^k c_1 σ^-k · c_1^-1 · σ^k c_1^-1 σ^-k`, adjacent `B`-letters merge only into
  `σ^(k-1)`, `σ^(-k)` and `σ^(k+1)`. These lie outside `C` for `k >= 2`. So `w_k` is a reduced
  alternating word of positive length, and it is nontrivial by the normal form theorem for amalgams. ∎

## Consequences

- **fp is not inherited.** `G_1` is finitely presented. So `Q` is finitely presented iff `ker θ` is
  finitely normally generated. The kernel contains the relations `w_k`, and their analogues built from
  `τ_ℓ = s^-ℓ σ s^ℓ`. These have sparse supports too, since `s^ℓ` has `N_ℓ <= N(2^ℓ - 1)` breakpoints per
  dyadic scale.
- **Finite presentation of Q is OPEN.** By `bhm-singfix-condition-forces-fp-germ-groups`, finite
  presentation of `Q` is necessary for certifying the host of the source node by Belk–Hyde–Matucci
  Theorem 2.1. Corollary 2.10 is unavailable, since `⟨σ⟩` is not normal in `Q` (it cannot be, by Lemma 5
  of `normal-germ-extensions-of-thompson-v-contain-no-sl3z`).

## Lesson for general BH

Piecewise-linear towers of coordinate changes always carry **sparse, commuting defects**. The top level
of the tower is a square map, and it must bend on every dyadic scale. The bends are a fixed number per
scale, so they are sparse, and the commutators they create commute with their far translates. So a PL
germ host never realizes a tower of height two faithfully. Its germ group is the tower group modulo
"lamplighter" relations between far-apart defects. This is the germ-level form of the lesson in
`higman-chain-group-pbh-iff-chain-configuration`: the host must let one element act on infinitely many
independent pieces. Here the pieces are the bends, and the extra relations are the price of that.

## Attempts

- **2026-09-19, swarm-0917-w15-w15-bh-follow: finite presentation of Q.** This is still OPEN. Here is
  what was tried and what came out of it.
  - *New coordinates.* Put `Λ(y) = 2^⌊y⌋(1+{y})`. Conjugating by `Λ` turns the square map `a` into
    `y ↦ 2y` and `δ` into `y ↦ y+1`, exactly. The zoom `σ` becomes a carry map `e_0` with bends at the
    integers. So `Q = M ⋊ BS(1,2)`, where `M = ⟨⟨σ⟩⟩` is the set of germs with `g(y) - y -> 0`.
  - *A subgroup represented exactly.* The germ group `⟨σ, ρσρ^-1⟩`, with `ρ = s^-1 δ s`, is represented
    exactly by its bend-local pictures in `PL(R)^2`. Explicit words in it satisfy the Cannon–Floyd–Parry
    relations, so `F ≤ M ≤ Q`. See `pl-chain-germ-group-contains-thompson-f`. So `Q` is not soluble,
    and soluble-group finiteness criteria cannot decide whether `Q` is finitely presented.
  - *Where the relations `w_k` live.* The relations `w_k` of this node live where `s = D_2` rescales
    pictures by factors that tend to infinity. These are limits of relations in
    `⟨ε, D_λ ε D_λ^-1⟩` as `λ -> ∞`.
  - *Dead ends.* Marked-group locality (`tail-uniform-germ-extensions-of-v-are-not-fp`) and a
    Bieri–Strebel splitting over the character `Q -> Z` were both tried. Both were inconclusive:
    `Q^ab = Z`, and every generator lies in a copy of `BS(1,2)`.
