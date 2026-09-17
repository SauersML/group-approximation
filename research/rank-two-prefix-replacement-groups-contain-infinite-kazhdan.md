---
rg: 2
id: rank-two-prefix-replacement-groups-contain-infinite-kazhdan
kind: claim
title: An infinite Kazhdan PGL_3 lattice acts on its Robertson–Steger boundary by rank-two prefix replacements, faithfully and with no invariant probability measure, so finiteness of Kazhdan subgroups is false for rank-two word systems and a proof for nV must use the product factorization
distinct_from:
  amenable-purely-infinite-groupoid-full-group-hosts-kazhdan: that realizes Z^3 x| SL_3(Z) in the full group of (M x| Gamma) x G_2, whose degree cocycle has a non-AF kernel, so it kills groupoid-generic proofs; this realizes a Kazhdan lattice by prefix replacements of a finite rank-two word system with Z^2 shape offsets, the same kind of structure nV has, so it kills word-system-generic proofs.
  input-encoded-sft-groupoid-hosts-are-not-universal: that shows rank-one word systems (shifts of finite type) host no infinite Kazhdan group; this shows the corresponding statement fails already in rank two.
  a2-group-embeds-in-full-group-of-its-rs-two-graph: that asks for an embedding into the Kumjian–Pask groupoid full group through Renault's reconstruction and has unpinned imports; this proves directly from the formula for φ that each lattice element acts as finitely many cylinder-to-cylinder prefix replacements, and adds property (T), faithfulness and the absence of invariant measures, with no groupoid identification.
  minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures: that is the open nV statement; this shows its rank-two word-system analogue is false.
artifacts:
  - research/artifacts/rank-two-prefix-replacement-kazhdan-2026-09-17.md
---

**ESTABLISHED** through `rank-two-prefix-replacement-kazhdan-proof` (unreviewed).

## Setting

- `K` is a nonarchimedean local field of characteristic zero, and `B` is the building of
  `PGL_3(K)`, with boundary `Ω` and base vertex `O`.
- `Γ` is a lattice in `PGL_3(K)` that acts on `B` by type rotating automorphisms, freely
  on vertices, with finitely many vertex orbits. Robertson–Steger state that concrete
  examples exist (`robertson-steger-boundary-cylinders-and-pure-infiniteness`, item 7).
- Notation for the word system is that of the same node: `A`, `M_1`, `M_2`, `W`, `W̄`,
  `𝔚̄_m`, the bijection `ᾱ`, and the cylinders `Ω(p)`.
- For `w̄ ∈ W̄` write `Ω[w̄] = Ω(ᾱ^{-1}(w̄))`.

**Prefix replacement.** Let `w̄_1, w̄_2 ∈ W̄` with `t(w̄_1) = t(w̄_2)`. A homeomorphism
`h: Ω[w̄_1] -> Ω[w̄_2]` is a *prefix replacement* `w̄_1 ⇒ w̄_2` when
`h(Ω[w̄_1 w]) = Ω[w̄_2 w]` for every `w ∈ W` with `o(w) = t(w̄_1)`. Its *shape offset* is
`σ(w̄_2) - σ(w̄_1) ∈ Z²`.

## Statement

1. `Γ` is infinite and has property (T).
2. For every `γ ∈ Γ` there is `m ∈ Z²_+` such that:
   - the clopen sets `Ω(p)`, `p ∈ 𝔚̄_m`, partition `Ω`;
   - for each `p` there is `p' ∈ 𝔚̄` with `γ|_{Ω(p)}` a prefix replacement
     `ᾱ(p) ⇒ ᾱ(p')`.

   So `γ` acts as finitely many prefix replacements with shape offsets in `Z²`.
3. `Γ` acts faithfully on `Ω`.
4. `Ω` carries no `Γ`-invariant Borel probability measure. Hence no closed invariant
   subset carries one (in particular no minimal set), and every `Γ`-orbit in `Ω` is
   infinite.

## Consequence for nV (class kill)

Call a result *word-system generic* if its proof uses only that `K` is finitely
generated, Kazhdan, and acts on a Cantor space whose cylinders are indexed by a finite
rank-two word system satisfying (H0)–(H3), each element acting by finitely many
prefix replacements with `Z²` shape offsets. By 1–4, every such result is false for
the following statements:

- (a) Kazhdan such `K` are finite;
- (b) Kazhdan such `K` have finite orbits
  (the analogue of `kazhdan-subgroups-of-nv-act-with-finite-orbits`);
- (c) every minimal set carries an invariant probability measure
  (the analogue of `minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures`).

So any proof of `kazhdan-subgroups-of-brin-thompson-groups-are-finite` for `n ≥ 2` has a
step that fails for `Γ ↷ Ω`.

**The invariant that must enter is the product factorization.**
- nV acts on `C^n` through a word system that is a product of rank-one full shifts:
  - tiles factor as `A = A_1 × A_2`;
  - `M_1 = J ⊗ I` and `M_2 = I ⊗ J`;
  - a shape-`m` cylinder is `[u_1] × [u_2]` with `|u_i| = m_i + 1`.
- A horizontal prefix replacement leaves the vertical letters untouched.
- In a Robertson–Steger system the letters of consecutive rows are coupled through the
  (H1) factorization squares. Changing a horizontal prefix changes the vertical coding
  by a finite-state sequential transducer, not by a prefix replacement. This is a
  heuristic description of the difference, not a proved statement.
- The description of nV as a product word system is the standard brick description.
  It is not formalized in the Robertson–Steger language here.
- Rank one is below the threshold: SFT full groups contain no infinite Kazhdan group
  (`input-encoded-sft-groupoid-hosts-are-not-universal`).

**Not asserted.**
- That `Γ` embeds in some nV (recorded under Attempts in the target claim as the
  negation route).
- The identification of `Ω` with the Kumjian–Pask path space.
