---
rg: 2
id: ct-z-frozen-tails-anywhere-give-kourovka-20-44
kind: claim
title: "For every finitely generated G ≤ CT(Z): if some point of the profinite integers has a frozen tail, G has an orbit transversal of positive lower density; so Kourovka 20.44 reduces to totally consumable groups, the slope-lattice geometry matters only there, and Kohl's 3x+1 group G_T is totally consumable"
distinct_from:
  ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44: that treats the positive ray by a chain argument; this proves the frozen half for every slope lattice, and keeps from the ray only its totally consumable half (the corner argument).
  ct-p-z-cone-avoiding-slope-lattices-trap-frozen-tails: that proves 20.44 where something freezes under cone-avoidance; this removes the hypothesis.
  ct-z-orbit-transversal-dichotomy-is-collatz-hard: that shows G_T has density-zero transversals; combined with this, G_T reads every depth from every point.
---

**ESTABLISHED** (lane proof, elementary, not reviewed). No priority claimed. Kourovka 20.44
(S. Kohl) stays **OPEN**. This node reduces it to one class.

## Setting (any slope lattice)

Let `G = ⟨S⟩ ≤ CT_P(Z)` (`P` finite), with inverse tables, depth `D`, degrees `n ∈ N^k` and
`m_n = ∏ p^(n_p)`.
- **Tracking, reading and freezing** are as in `ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44`.
- **Two facts** are proved there without the ray hypothesis:
  - a word shifts every unread degree by the same vector, namely its degree cocycle `c ∈ Λ(G)`;
  - the inverse word, with inverse tables, returns every unread tail to its degree.
- **Frozen sets.** `E(y)` is the set of degrees frozen at `y`. `Y_K = {y ∈ Ẑ : K ∈ E(y)}` is a
  union of classes mod `M_K = m_K Π^D`, where `Π = ∏_{p∈P∪{2}} p`.
- **Totally consumable.** `G` is *totally consumable* if `E(y) = ∅` for every `y ∈ Ẑ`.

**Lemma 1.** If `y′ = h y` and `c = c(h, y)`, then `E(y′) = E(y) + c`.

*Proof.*
- A frozen tail at `d ∈ E(y)` is unread along `h`, so it lands at `d + c ≥ 0`. Any word reading
  it from `y′` would, after `h`, read it from `y`. So `d + c ∈ E(y′)`.
- By reversal, `h^(−1)` shifts unread degrees by `−c`. If `d′ ∈ E(y′)`, its tail lands at
  `d′ − c` in `y`, and it is frozen there by the same concatenation argument. ∎

**Lemma 2 (uniform count).** Every orbit `O` contains at most
`A_K = Σ_{c ∈ Λ, −K ≤ c ≤ K} m_(K+c)` points `y` with `K ∈ E(y)`.

*Proof.*
- Fix such a `y_0 ∈ O`, and let `y = h y_0` with `K ∈ E(y)` and `c = c(h, y_0)`.
- The tail of `y_0` at `K` lands at `K + c`, so `c ≥ −K`.
- By Lemma 1, `K − c ∈ E(y_0) ⊆ N^k`, so `c ≤ K`.
- Then `y = ρ + m_(K+c)·σ^K(y_0)` with `0 ≤ ρ < m_(K+c)`. ∎

**No cone hypothesis appears.** The frozen set itself caps the shift from above, and the position
caps it from below.

## Theorem

Let `G ≤ CT(Z)` be finitely generated.
1. **Frozen somewhere ⇒ 20.44.** If `Y_K ≠ ∅` for some `K`, then:
   - `G` has infinitely many orbits on `Z`;
   - for `N ≥ M_K`, at least `δ_K N / (2A_K)` orbit minima lie in `[0, N]`, where
     `δ_K = μ(Y_K) ≥ 1/M_K`;
   - the same holds on `[−N, −1]`.
2. **Reduction.** Kourovka 20.44 holds iff every totally consumable finitely generated `G ≤ CT(Z)`
   has finitely many orbits or a transversal of positive density.

*Proof.*
- **1.** `[0, jM_K)` contains `δ_K j M_K` points of `Y_K`, and each orbit contains at most `A_K`
  of them (Lemma 2). So at least `δ_K j M_K / A_K` distinct orbits meet `[0, jM_K)`, each with
  its minimum there. Take `j = ⌊N/M_K⌋`.
- **2.** Immediate from 1. ∎

## Where the slope-lattice geometry now acts: totally consumable groups only

| Slope lattice `Λ` | Totally consumable `G` |
|---|---|
| positive ray `Zv`, `v ≥ 0` | finitely many orbits: the corner argument (ray node, item 1) meets every orbit in `[−Π^D, Π^D)` |
| cone-avoiding (trapped; e.g. `⟨3/2, 5/2⟩`) | open. Tails are read only at the ends of finite level sets, and the configuration there need not be small (sweeping) |
| `dim C_Λ = 1`, `rank Λ ≥ 2` (e.g. slopes `2` and `3/5`) | open. Reading can happen at the transversal ends of a tube, at any depth along the ray |
| `dim C_Λ = 2` (e.g. Kohl's `G_T`, slopes `2` and `3/2`) | Collatz-hard: for `G_T`, 20.44 ⟺ the 3x+1 map has finitely many components on `Z` |

Here `C_Λ = span_R(Λ) ∩ R^k_(≥0)`.

**Corollary (G_T reads every depth).** `G_T` is totally consumable: from every point of `Ẑ`, every
degree is eventually read.
- By `ct-z-orbit-transversal-dichotomy-is-collatz-hard`, `ν_(G_T)(N) = o(N)`. That rules out 1.
- This is unconditional. Only the finiteness of its orbits is Collatz-strength.

**The first dimension-2 case.** `G_T` is it. Frozen tails would make it tame, and there are
none, so all of its difficulty sits in the totally consumable class, as the conjecture predicts.

## Lesson for general BH

**Frozen information always gives tameness; hardness needs total consumption.**
- In every arithmetic host `CT_P(Z)`, one frozen tail anywhere yields a positive-density family of
  orbit invariants. The frozen set caps the shift from above and the position caps it from below,
  whatever the slopes.
- So every hard orbit question (Collatz, and 20.44 in general) lives among groups that read every
  depth from every point.
- The slope geometry decides only how such total consumption behaves:
  - bounded, at the corner of a positive ray;
  - sweeping, on trapped level sets and along tube ends;
  - Collatz, in dimension 2.
