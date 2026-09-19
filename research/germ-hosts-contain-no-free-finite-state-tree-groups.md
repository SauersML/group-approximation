---
rg: 2
id: germ-hosts-contain-no-free-finite-state-tree-groups
kind: claim
title: Finite-state tree automorphisms in a cone-closed germ host have polynomial activity, so no free group acts by them there; hence ascending HNN extensions of F_n (n ≥ 2) cannot enter the germ host class through self-similar realizations
distinct_from:
  germ-host-class-closed-under-sectioned-ascending-hnns: that is the closure theorem for the class 𝓒_d; this bounds its reach, showing which realizations of free-group mapping tori it cannot use.
  ascending-hnn-of-free-groups-satisfy-boone-higman: that proves BH for all F_n*_φ through BLIW's generalized Baumslag–Solitar class; this concerns only whether the germ-host route can reach them, not their BH status.
---

**ESTABLISHED** (lane proof below; the only literature input is Sidki's theorem, cited and
not re-read; not reviewed).

## Statement

Let `W ∈ 𝓒_d` and let `S ≤ W ∩ Aut(T_d)` consist of finite-state tree automorphisms. Then:

1. every element of `S` has polynomial activity;
2. `S` contains no non-abelian free subgroup;
3. **(free groups).** For `n ≥ 2` and `φ: F_n → F_n` injective, `F_n` has no faithful action
   by finite-state tree automorphisms inside a member of `𝓒_d`. In particular, none in which
   `φ` is cone-sectioned. Such cone-sectioned tree actions do exist; they are only excluded
   from `𝓒_d`.
4. **(rank 1).** For `φ(x) = x^m` with `m ≥ 2`, the `m`-ary odometer `τ` gives a
   cone-sectioned realization: `τ^m = (τ, …, τ)`. Its tail group is `Z`,
   so `BS(1,m)` enters `𝓒` from the bounded seed `V_m⟨τ⟩`. This is a calibration only.

So for free groups, the germ-host route needs **asynchronous** realizations, meaning
cone-sectioned actions by non-tree elements of Thompson-like groups. Whether any `F_n*_φ` with
`n ≥ 2` and `φ` non-surjective admits one in some member of `𝓒_d` is **open**. (BH for these
groups is already known by other means.)

## Proof

- **Singular points of a tree automorphism.** For `g ∈ Aut(T_d)` and `x ∈ C`, `g` agrees with
  an element of `V_d` near `x` iff some section `g|_{x_1⋯x_n}` is trivial. One direction: a
  level-preserving prefix replacement `αw ↦ βw` has `|α| = |β|`, so `g|_α = 1`. The other is
  clear. So `sing(g)` is the set of rays along which every section is nontrivial.
- **Countable iff polynomial activity.** For finite-state `g`, these rays are the infinite
  paths from `g` through nontrivial states of its automaton. Distinct paths read distinct input
  words, since the automaton is deterministic. Two distinct cycles through a common reachable
  nontrivial state give uncountably many such paths. Otherwise the paths are countable, and
  this is exactly polynomial activity (Sidki's cycle criterion).
- **Parts 1 and 2.** By (C2), `sing(g) ⊆ sing(W)` is countable, so `g` has polynomial activity
  (part 1). Sidki, *Finite automata of polynomial growth do not generate a free group* (Geom.
  Dedicata 108, 2004; cited, not re-read), gives part 2.
- **Part 3, exclusion.** Immediate from part 2.
- **Part 3, existence.** By M. Hall's theorem there is a finite-index `D ≤ F_n` in which
  `φ(F_n)` is a free factor, `D = φ(F_n) * L`. Define `π: D → F_n` by `π = φ^{-1}` on
  `φ(F_n)` and arbitrarily on `L`. Then `π∘φ = id`, and the self-similar action on the coset
  tree of `D` (letter `L` ↔ coset `D`) has `φ(g)|_L = π(φ(g)) = g`. Faithfulness of this
  action is not claimed; it is excluded from `𝓒_d` whenever it is faithful.
- **Part 4.** `τ^m` fixes the first letter and has all sections `τ`. So `σ(τ^j) = τ^{mj}` is
  cone-sectioned, with `ψ(τ^j) = (τ^j, …)`, and the tail `τ^j ↦ (τ^{m^k j})_k` is injective.

## Lesson for general BH

(C2), the requirement that singularities be countable and rational, is what gives germ hosts
their finiteness. It also rules out free groups acting by finite-state tree automorphisms,
because polynomial activity is the tree shadow of countable singularities. So the class `𝓒`
reaches dilation dynamics (Baumslag–Solitar, Basilica) but can reach free-group mapping tori
only asynchronously.

This separates two BH mechanisms:
- BLIW trees of groups, which handle free groups;
- germ hosts, which handle amenable branch-type groups.

A master route for BH likely needs a bridge between them: a germ host containing an
asynchronous cone-sectioned free group.
