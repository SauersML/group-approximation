---
rg: 2
id: digit-letters-are-relatively-convex-but-not-positively-connected
kind: claim
title: The free digit-letter subgroup F(a) of BS_k(1,m) is left relatively convex (it is a free factor of the free group H = preimage of <a> under BS_k(1,m) -> BS(1,m)), but the resulting lexicographic order fails positive connectivity, because (PC) forces the relative positive cone to be finitely generated modulo F(a) while H is free of infinite rank
distinct_from:
  ordered-orbits-give-rigid-relative-seeds: that builds a rigid relative seed from any invariant order with (PC) and (DO); this answers whether its route applies to (BS_k(1,m), F(a)): relative convexity holds, and the natural order violates (PC).
  digit-group-cores-need-m-adic-coherence: that blocks the tree-gluing route to (Z_J, F(a)); this examines the order route instead.
---

**Status.**
- §§1–3 are **ESTABLISHED** (lane proof, bh-invent-14, 2026-09-19; elementary; not reviewed).
- The step "free factors are left relatively convex" is **recalled, not re-read**. It is due to
  Chiswell (vertex groups of a graph of left-orderable groups with relatively convex edge groups are
  relatively convex), and is also in Antolín–Dicks–Šunić, *Left relatively convex subgroups*.
- §4 is open.
- Inputs: `ordered-orbits-give-rigid-relative-seeds` (bh-invent-03, 8a8a52553f), which answers the
  lead's question (iv) of 09-19, and `digit-group-cores-need-m-adic-coherence`.

**Notation.**
- `Z_J = ⟨x, a_1, …, a_k | a_i^{-1} x a_i = x^m⟩`, with `k ≥ 2` and `m ≥ 2`, and `T` is its
  Bass–Serre tree over `⟨x⟩`.
- `π : Z_J → BS(1,m) = ⟨x, a | a^{-1} x a = x^m⟩` is the map `a_i ↦ a`.
- `H = π^{-1}(⟨a⟩)`.
- A subgroup `C ≤ G` is *relatively convex* if `G/C` carries a `G`-invariant linear order.

## 1. `H` is free and `F(a)` is a free factor of `H`

- **Free action.** A conjugate `g x^j g^{-1}` with `j ≠ 0` maps to a nonzero element of `Z[1/m]`,
  which does not lie in `⟨a⟩`. So `H` meets every vertex stabilizer of `T` trivially, acts freely on
  `T`, and is free.
- **Free factor.**
  - Let `T_F` be the core of `F(a)`, with vertices `w⟨x⟩` for `w ∈ F(a)`.
  - If `h ∈ H` maps a core vertex `w⟨x⟩` to a core vertex `w'⟨x⟩`, then `w'^{-1} h w ∈ ⟨x⟩ ∩ H = 1`,
    so `h ∈ F(a)`.
  - So the translates `h T_F` are pairwise disjoint or equal, and `F(a)\T_F` embeds as a connected
    subgraph `Γ'` of `H\T`, with `π_1(Γ') = Stab_H(T_F) = F(a)`.
  - The fundamental group of a connected subgraph is a free factor of the fundamental group of the
    whole graph: extend a spanning tree of `Γ'`.
- **Infinite rank.**
  - `H\T` has infinitely many vertices, since `H\Z_J/⟨x⟩ ≅ ⟨a⟩\BS(1,m)/⟨x⟩ ≅ Z[1/m]/Z`. Every
    double coset has a representative `(q, 1)`, unique modulo `Z`.
  - `H\T` is locally isomorphic to `T`, of valence `k(m+1) ≥ 6`.
  - So `H` has infinite rank.

## 2. `F(a)` is relatively convex in `Z_J`

- **`H` is relatively convex in `Z_J`.** `Z_J/H ≅ BS(1,m)/⟨a⟩ ≅ Z[1/m]`, as the orbit of `0` under
  the affine action (`x : t ↦ t+1`, `a : t ↦ t/m`). That action preserves the order of `R`.
- **`F(a)` is relatively convex in `H`.** It is a free factor (§1), and free factors are relatively
  convex (recalled; see Status).
- **Transitivity.**
  - Order `Z_J/F(a)` lexicographically: first by the image in `Z_J/H`, then within each fibre
    `gH/F(a) ≅ H/F(a)`, identified by `ghF(a) ↦ hF(a)`.
  - Changing `g` to `g h_0` changes the identification by left multiplication by `h_0`. The fibre
    order is `H`-invariant, so it is well defined.
  - The result is `Z_J`-invariant. ∎

So the answer to question (iv) is **yes**: `F(a)` is relatively convex in `BS_k(1,m)`.

## 3. The lexicographic order fails (PC)

**(PC) is a finiteness condition on the relative cone.** In the setting of
`ordered-orbits-give-rigid-relative-seeds`, let `P = {g : gω_0 > ω_0}`. A chain of positive
neighbours from `ω_0` to `gω_0` is a factorization `g ∈ C s_1 C s_2 ⋯ C s_r C` with `s_i ∈ S^+`.
- So (PC) says that `P ⊆ ⟨C ∪ S^+⟩_{semigroup}·C`.
- That is, the relative positive cone is finitely generated modulo `C`.

**Failure for the lexicographic order.**
- Fibres `gH/F(a)` are convex blocks, and every step of a chain moves up.
- So a chain from `ω_0` to a point of its own fibre never leaves the fibre. All its letters `s_i`
  lie in `S ∩ H`, and all its `C`-factors lie in `F(a) ⊆ H`.
- Hence `P ∩ H ⊆ H_0 := ⟨F(a), S ∩ H⟩`, a finitely generated subgroup of `H`.
- But `H = (P ∩ H) ∪ (P ∩ H)^{-1} ∪ F(a)`, so `H = H_0` would be finitely generated. This
  contradicts §1. ∎

**The same argument in general.** Whenever a relatively convex order on `G/C` has a convex block
`gK/C` for an intermediate subgroup `C ≤ K ≤ G` with `K` not finitely generated, (PC) fails.

## 4. Open: a non-lexicographic order

- **What is needed.** The order route needs a `Z_J`-invariant order on `Z_J/F(a)` whose positive cone
  is finitely generated modulo `F(a)`, plus a dense orbit.
- **What the order must avoid.** By §3, no infinitely generated intermediate subgroup may have convex
  cosets. In particular `H` may not.
- **Equivalent form.** An action of `Z_J` on the line with `Stab(0) = F(a)`, in which the positive
  steps `g c s(0)` reach every higher orbit point exactly.
- **The natural candidate.** Perturb the affine action (`a_i(t) = t/m + ε_i p(t)`, with `p`
  `m`-periodic and `p(0) = 0`), so that `Stab(0)` drops from `H` to `F(a)`.
  - This keeps the orbit dense.
  - But exact landing (PC) is an arithmetic property. In `BS(1,m)` it comes from base-`m` digits, and
    it is not expected to survive a generic perturbation.

## Lesson for general BH

**Orders see the same wall as trees.**
- Relative convexity is cheap: it holds for the digit letters through a free-factor argument.
- A rigid order seed needs more. Its relative positive cone must be finitely generated modulo the
  subgroup, and that is exactly where the machine's `m`-adic counting hides.
- The natural order factors through `BS(1,m)`. It makes the infinitely generated group `H` a convex
  block, and positive chains cannot move inside such a block.
- So on both routes, trees and orders, the obstruction is one and the same: `k` free digit letters
  over one distorted cyclic group. A seed must realize the counter's positions as reachable in
  finitely many generator types, and base-`m` digits do this only when `k = 1`.
