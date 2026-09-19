---
rg: 2
id: fp-self-similar-finitely-supported-loops-give-characters-proof
kind: route
title: Proof of the loop character by treating eventual sections along the cofinality class as a finitely supported H_xi-valued cocycle and summing its abelianization over the class
target: fp-self-similar-finitely-supported-loops-give-characters
requires:
  - fp-self-similar-groups-have-fp-ray-loop-subgroups
  - fully-self-replicating-fp-infinity-groups-are-acyclic
  - tits-hosts-for-transitive-local-actions
artifacts:
  - experiments/m11-separated-loop-host-2026-09-18/separated_loop_checks.py
  - experiments/m11-separated-loop-host-2026-09-18/separated_loop_checks.out
---

**Conventions.** Right actions: `(xw)^g = x^{π_g} w^{g|_x}` and `(gh)|_v = g|_v h|_{v^g}`.
`p_m(η)` is the length-`m` prefix of an end `η`, and `p_m(η)^g = p_m(η^g)`.

**Step 1 (item 1).** Write `g = s_1 ⋯ s_n` with `s_i ∈ S`, and put `η_1 = η`,
`η_{i+1} = η_i^{s_i}`. By the product rule,

`g|_{p_m(η)} = s_1|_{p_m(η_1)} s_2|_{p_m(η_2)} ⋯ s_n|_{p_m(η_n)}`.

By (Ω) every `η_i` lies in `Ω`. By (E) each factor equals `c(s_i, η_i)` for all large `m`.
So `g|_{p_m(η)}` is eventually constant, with value `∏_i c(s_i, η_i) ∈ H_ξ`. The value is
a function of the automorphism `g` and of `η`, not of the word: it is the eventual section
of `g` itself. Call it `κ(g, η)`. (This is (F1) of the proof of
`fp-self-similar-groups-have-fp-ray-loop-subgroups`.)

- **Cocycle.** For large `m`, `(gh)|_{p_m(η)} = g|_{p_m(η)} h|_{p_m(η^g)}`, so
  `κ(gh, η) = κ(g, η) κ(h, η^g)`.
- **Support.** By the displayed product, `κ(g, η) ≠ 1` only if `c(s_i, η_i) ≠ 1` for some
  `i`, that is, only if `η ∈ (s_1 ⋯ s_{i−1})^{−1}(supp s_i)` for some `i`. This is a finite
  union of finite sets, by (FS). ∎

**Step 2 (item 2).** `Φ(g)` is a finite sum, by Step 1. For `g, h ∈ G`,

`Φ(gh) = Σ_η [κ(g, η)] + Σ_η [κ(h, η^g)] = Φ(g) + Φ(h)`,

because `η ↦ η^g` is a bijection of `Ω` by (Ω). ∎

**Step 3 (item 3).** `Φ(G)` is the image of a finitely generated group, so it is a finitely
generated abelian group. `Φ` factors through `H_1(G; Z)`, so `rank H_1(G; Z) ≥ rank Φ(G)`.

For the special case, every `c(s, η)` lies in `⟨t⟩`, so `H_ξ ⊆ ⟨t⟩`. Also `t = κ(t, ξ)`,
because `y^t = y` and `t|_y = t` give `t|_{y^m} = t` for all `m`. So `H_ξ = ⟨t⟩ ≅ Z`,
because `t` has infinite order. The only nonzero term of `Φ(t)` is at `ξ`, so `Φ(t) = [t]`,
a generator of `Z`. Hence `Φ : G → Z` is onto. ∎

**Step 4 (item 4).** If `Φ(G)` is infinite, `Φ(G) ⊗ Q ≠ 0` is a quotient of
`H_1(G; Q)`. Now apply item 3(a) of `fully-self-replicating-fp-infinity-groups-are-acyclic`
with `a = 1`: a group `G ≅ G ≀_X P` with `P ≤ Alt(X)` and `H_1(G; Q) ≠ 0` has
`H_{d−1}(G; Q)` infinite-dimensional, so it is not `FP_{d−1}` over `Q`. `FP_∞` implies
`FP_{d−1}`.

*The host.* The Tits host of `tits-hosts-for-transitive-local-actions` is
`Γ⁺ = A *_C A'` with `A ≅ A' ≅ G ≀ F` and `C = G × G`. Suppose `Γ⁺` is `FP_n` over `Q`.
We show by induction on `j ≤ n` that `G` is `FP_j` over `Q`. For `j = 1` this holds
because `G` is finitely generated. If `G` is `FP_{j−1}`, then so is `C = G × G`. For an
amalgam of type `FP_j` over an edge group of type `FP_{j−1}`, the vertex groups are
`FP_j` (Bieri's Mayer–Vietoris argument). So `A` is `FP_j`. `A` contains `G^{d+1}` with
finite index, and `G` is a retract of `G^{d+1}`, so `G` is `FP_j`. Taking `n = d − 1`, the
host is not `FP_{d−1}` over `Q`. If `rank Φ(G) ≥ 2`, then `dim H_1(G; Q) ≥ 2`, and
item 3(d) there forbids finite presentation. ∎

**Remarks.**

- The construction is the abelian shadow of the covering group in the ray-loop proof. There,
  the fibre coordinate over `Ω` records the word `W_η(w)` in `F(C)`. Here we evaluate it in
  `H_ξ^{ab}` and add over the class, which is legitimate exactly when (FS) makes the sum
  finite.
- (FS) is a condition on the generators, and it is checked on the automaton. The support of
  `s` is the set of ends `v y^∞` along which the automaton path from `s` reaches a nontrivial
  loop state of `ξ` and stays on it. It is infinite as soon as a path from `s` runs through
  a cycle of the automaton, leaves it, and then reaches such a loop state; it is finite when
  no such path exists. Example: for `R' = ⟨M_11, b, c'⟩` of
  `m11-separated-loop-host-has-b1-one`, (FS) fails at `1^∞`, because `c'` loops at `4` and
  exits to `bα`, which reaches `b` (support `{4^k 5 1^∞}`). It holds at `4^∞`.
