---
rg: 2
id: ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44
kind: claim
title: "Kourovka 20.44 holds for every finitely generated subgroup of CT_P(Z) (P finite) whose slopes all lie in γ^Z for one integer γ ≥ 2: either at most 2Π^D orbits on Z, or orbit minima of positive lower density; the frozen tail survives any number of primes as long as the degree cocycle stays on a ray of the positive cone"
distinct_from:
  ct-empty-z-subgroups-satisfy-the-orbit-transversal-dichotomy: that is the one-prime case P = ∅ (γ = 2); this allows any finite P, with carries in every coordinate, and needs only that the degree cocycle is confined to one positive ray.
  periodic-k-graph-subgroups-with-ray-cocycle-are-finite: that proves torsion local finiteness under the same ray hypothesis by pumping; this proves the orbit-transversal dichotomy under that hypothesis by a frozen-tail invariant.
  ct-z-orbit-transversal-dichotomy-is-collatz-hard: that is the wild side (Kohl's G_T, rank-2 cocycle, equivalent to 3x+1 finiteness); this is the tame side.
---

**ESTABLISHED** (lane proof, not reviewed). Elementary. No priority claimed.
- **Problem.** Kourovka 20.44 (S. Kohl). The general case stays **OPEN**, and it is 3x+1-hard
  (`ct-z-orbit-transversal-dichotomy-is-collatz-hard`).
- **What this adds.** It extends `ct-empty-z-subgroups-satisfy-the-orbit-transversal-dichotomy`
  from one prime to any finite `P`, under the same ray condition that bh-kourovka's pumping
  theorem uses for torsion (`periodic-k-graph-subgroups-with-ray-cocycle-are-finite`).

## Setting

- **Notation.** `P` is a finite set of odd primes, `P' = P ∪ {2}`, `k = |P'|` and
  `Π = ∏_{p∈P'} p`. For `n ∈ N^k` put `m_n = ∏ p^(n_p)`.
- **Boxes and tails.** Following `ct-p-z-is-a-one-vertex-k-graph-full-group`:
  - `CT_P(Z)` is the full group of the one-vertex `k`-graph with path space `Ẑ = ∏_{P'} Z_p`;
  - a class `r(m_d)` is a cylinder of degree `d`;
  - a canonical piece `r + m_d z ↦ s + m_(d') z` is a prefix replacement `λz ↦ μz` with
    `d(λ) = d` and `d(μ) = d'`.
  - The *tail* at degree `n` is `σ^n x = (x − ρ_n(x))/m_n`, where `ρ_n(x) ∈ [0, m_n)` and
    `ρ_n(x) ≡ x mod m_n`. It satisfies `σ^(n+n') = σ^(n') σ^n`, and `σ^n x = ⌊x/m_n⌋` for
    `x ∈ N_0`.
- **The group.** `G = ⟨S⟩`, with `S` finite and symmetric, given by tables of pieces; `s^(-1)`
  carries the inverse table. `D` is chosen with every piece degree `≤ D·1`.
- **Ray hypothesis.** There is `v ∈ N^k ∖ {0}` with `d(μ) − d(λ) ∈ Zv` for every piece. In
  other words, every slope lies in `γ^Z` for `γ = m_v ≥ 2`.

**Tracking.** Let `x = r + m_d z` lie in a piece, and let `K ≥ d(λ)`.
- Then `σ^K x = σ^(K − d(λ)) z = σ^(K + d(μ) − d(λ))(s + m_(d') z)`. So the move carries the
  tail at degree `K` unchanged to degree `K + d(μ) − d(λ)`.
- If `d(λ) ≰ K`, the move *reads* `K`. A degree `K` is **consumable from `x`** if some word
  reads the tail that starts at `K`.
- Three facts transfer verbatim from the one-prime node:
  - **Uniform shift.** One move shifts every unread degree by the same vector.
  - **Monotonicity.** Consumable degrees form a down-set in `N^k`.
  - **Reversal.** Inverse tables undo each step, so an unread tail returns to its degree.
- **Only a prefix matters.**
  - Before the tail at `K` is read, a configuration is `w = ρ + m_p·σ^K x`.
  - Its piece is fixed by `w mod Π^D`, i.e. by `ρ` and `σ^K x mod Π^D`.
  - So consumability of `K` depends only on `x mod M_K`, where `M_K = m_K Π^D`. The set
    `C_K` of points from which `K` is consumable is a union of classes mod `M_K`.

**The chain.** Put `K_s = s v + D·1`, for `s` in `R = {s ∈ Z : K_s ∈ N^k} = [s_0, ∞)`.
- By the ray hypothesis a word shifts unread degrees by elements of `Zv`. So a tail that starts
  on the chain stays on it.
- `K_s ≤ K_(s+1)`, so by monotonicity `δ_s = μ(Ẑ ∖ C_(K_s))` is nondecreasing, where `μ` is
  Haar measure.

## Theorem

1. **Few orbits.** If `δ_s = 0` for all `s ≥ 0`, then every orbit on `N_0` meets `[0, Π^D)`,
   and every orbit on the negative integers meets `[−Π^D, 0)`. So `G` has at most `2Π^D` orbits
   on Z.
2. **Dense minima.** If `δ_s > 0`, put `A_s = Σ_{s_0 ≤ s' ≤ s} m_(K_(s'))`. For
   `N ≥ M_(K_s)`, the orbit minima in `[0, N]` number at least `δ_s N / (2A_s)`, and the same
   holds on `[−N, −1]`.

So every finitely generated subgroup of `CT_P(Z)` whose slopes lie in one `γ^Z` satisfies the
dichotomy of Kourovka 20.44.

## Proof

**1.**
- `C_(K_s)` is clopen with complement of measure 0, so `C_(K_s) = Ẑ`.
- For `x ∈ N_0`, pick `s ≥ 0` with `m_(K_s) > x`. Then `σ^(K_s) x = 0`, and some word reads it.
- Just before the reading move, the tail sits at some chain degree `K_(s')`. The move has
  `d(λ) ≤ D·1` and `d(λ) ≰ K_(s')`, so some coordinate of `s'v + D·1` is `< D`.
- That forces `s' < 0`, and hence `K_(s') ≤ D·1`.
- The configuration `w` then has tail `0` at `K_(s')`. So `w = ρ_(K_(s'))(w) ∈ [0, Π^D)`, and
  `w` is in the orbit of `x`.
- For negative `x` the tail is `−1`, so `w ∈ [−Π^D, 0)`. ∎

**2, step 1: frozen tail.**
- Let `κ(x)` be the least `s ∈ R` with `K_s` non-consumable, and `T(x) = σ^(K_(κ(x))) x`.
- **Claim.** Let `y = P(x)`, and let `P` shift unread degrees by `tv`. Then
  `κ(y) = κ(x) + t` and `T(y) = T(x)`.
  - **`κ(y) ≤ κ(x) + t`.** The tail of `x` at `K_(κ(x))` arrives at `K_(κ(x)+t)`. A word that
    reads it from `y` would, after `P`, read it from `x`.
  - **`κ(y) ≥ κ(x) + t`.**
    - `Q = P^(-1)` does not read `K_(κ(y))` or anything above it, and it shifts those degrees
      uniformly.
    - It returns the tail at `K_(κ(x)+t)` to `K_(κ(x))` (reversal), so its shift is `−tv`.
    - So `K_(κ(y))` of `y` lands at `K_(κ(y)−t)` of `x`, and a word reading it from `x` would,
      after `Q`, read `K_(κ(y))` from `y`. Hence `κ(x) ≤ κ(y) − t`.
  - **Tails.** `T(y) = σ^(K_(κ(x)+t)) y = σ^(K_(κ(x))) x = T(x)`, by tracking.

**2, step 2: counting.**
- The event `{κ ≤ s}` is exactly "`K_s` non-consumable", a union of classes mod `M_(K_s)`. So
  `[0, jM_(K_s))` contains exactly `δ_s j M_(K_s)` of its points.
- A point with `κ(x) = s'` and `T(x) = T` is `ρ + m_(K_(s')) T` with `0 ≤ ρ < m_(K_(s'))`. So
  an orbit meets `{κ ≤ s}` in at most `A_s` points.
- Hence at least `δ_s j M_(K_s) / A_s` orbits meet `[0, jM_(K_s))`, and their minima are
  distinct.
- Taking `j = ⌊N/M_(K_s)⌋ ≥ N/(2M_(K_s))` gives the bound. Negatives are the same. ∎

## Where the line falls

| Degree cocycle of `G` | Kourovka 20.44 | f.g. torsion subgroups |
|---|---|---|
| on a positive ray `Zv`, `v ≥ 0` | **true** (this node) | finite (`periodic-k-graph-subgroups-with-ray-cocycle-are-finite`) |
| rank 2, e.g. Kohl's `G_T` (slopes `2`, `3/2`) | ⟺ 3x+1 has finitely many components on Z | open |
| mixed-sign ray, e.g. slopes in `(3/2)^Z` | open | open |

- **Carries are not the obstruction.** Take `v = (1, 0)` in `CT_{{3}}(Z)`.
  - The classes `r(2^a 3^b)` are not 2-adic cones.
  - `τ_{1(3), 0(6)}` has slope `2`, but on the 2-adic coordinate it is `x ↦ 2(x − 1)`, which
    has borrow chains of unbounded length.
  - Yet the theorem applies.
- **What matters is the direction of the drift.** A tail drifts along a line through the
  positive cone, so it can only be read near the corner `D·1`, where configurations are bounded.
- **The Collatz escape.** With a rank-2 or mixed-sign cocycle, a tail slides along a face of
  the cone, to degree `(0, huge)`, and is read far out. That is where 3x+1 lives.

## Lesson for general BH

**The tame/wild line for arithmetic hosts is the cone position of the subgroup's degree
cocycle, not the number of primes or the carries.**
- On a positive ray, a subgroup has a frozen-tail invariant. From it follow torsion local
  finiteness and the orbit-transversal dichotomy, both by one bounded-corner argument.
- Off the ray (rank 2 or mixed sign), both questions become Collatz-type.

**For host design.** A subgroup whose behaviour must be controlled, such as an embedded input
that must stay finitely generated with tame orbits or torsion, should be placed so that its
cocycle lies on one positive ray. Hardness, such as periodic monsters or undecidable dynamics,
must be sought in cocycles of rank 2 or of mixed sign.
