---
rg: 2
id: nishikawa-petrosyan-equivariant-power-functor-citation
kind: route
title: Apply Nishikawa–Petrosyan Theorems 5.10 and 5.16, Lemma 5.15 and Proposition 5.18
target: nishikawa-petrosyan-equivariant-power-functor
requires: []
---

**Source.** Shintaro Nishikawa and Nansen Petrosyan, *Dehn fillings, equivariant homology, and the
Baum–Connes conjecture*, arXiv:2509.15070v2 (8 Oct 2025). Read from the PDF on 2026-09-13.

- **Item 1: Theorem 5.10 (p. 31) and Definition 5.13 (p. 36).**
  - Theorem 5.10 constructs the map
    `⊗̂_Ω : KK_G(A, B) → KK_(G≀_Ω F)(A^(⊗̂Ω), B^(⊗̂Ω))`. It satisfies
    - (1) \*-homomorphisms go to tensor powers;
    - (2) compatibility with products against \*-homomorphisms on both sides;
    - (3) `KK_G`-equivalences go to `KK_(G≀_Ω F)`-equivalences.
  - "The restriction of `⊗̂_Ω` to the subcategory of the separable ungraded C\*-algebras is a functor
    from `KK_G` to `KK_(G≀_Ω F)`, and it is a unique functor satisfying the first condition (1) above."
  - The cycle-level construction uses the `S_N`-symmetric partition of Theorem 5.11 (p. 33).
    Remark 5.12 warns that naive `S_N`-averaging of a standard partition fails for `N ≥ 3`.
- **Item 2: Lemma 5.15 (p. 37).**
- **Item 3: Theorem 5.16 (p. 37).** "If `G` has a gamma element `γ_G` in `KK_G(C, C)` in the Meyer–Nest
  sense, then for any second countable, compact group `F` and for any finite `F`-set `Ω`, `G ≀_Ω F`
  has a gamma element `γ_(G≀_Ω F)` in `KK_(G≀_Ω F)(C, C)` in the Meyer–Nest sense, and
  `γ_(G≀_Ω F) = ⊗̂_Ω(γ_G)`."
- **Item 4.**
  - The Izumi filtration, recalled on p. 37 from Kranz–Nishikawa [KN25], Definition 3.10 and
    Proposition 3.9.
  - Proposition 5.18 (pp. 38–40): for the mapping cone/cylinder sequence `0 → C_φ → M_φ → B → 0`,
    every step `0 → I_(j+1) → I_j → I_j/I_(j+1) → 0` with `0 ≤ j ≤ |Ω| − 1` admits a
    `G ≀_Ω F`-equivariant c.c.p. section.
  - Lemma 5.19 (p. 40): `A ∈ <CI_G>` implies `A^(⊗Ω) ∈ <CI_(G≀_Ω F)>`.
