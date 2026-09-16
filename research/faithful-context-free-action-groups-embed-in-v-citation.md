---
rg: 2
id: faithful-context-free-action-groups-embed-in-v-citation
kind: route
title: "Import: faithful context-free actions give subgroups of V (Bodart-D'Angeli-Perego-Rodaro Thm A, Thm 2.9)"
target: faithful-context-free-action-groups-embed-in-v
requires: []
artifacts:
  - research/artifacts/twisted-power-cloning-cf-action-2026-09-16.md
---

Literature import, not a reproof.

C. Bodart, D. D'Angeli, D. Perego, E. Rodaro, *A graph-theoretical
characterisation of subgroups of Thompson's group V*, arXiv:2608.02111v1
(submitted 3 Aug 2026). PDF fetched and read 2026-09-16.

- Definitions 1.1–1.8 (pp. 4–7): inverse `A`-graphs; the transition group
  `G(Γ) ≤ Sym(VΓ)`; `L(Γ,x)` = labels of cycles at `x`; a *context-free graph*
  is a connected inverse graph with `L(Γ,x)` context-free for one (equivalently
  all) `x`; an action `X ↶ G` of `G = ⟨A⟩` is *context-free* if it has finitely
  many orbits and all orbital Schreier graphs `Sch(ξ,G;A)` are context-free;
  `G` is `CF-TR` iff `G ≃ G(Γ^(1) ⊔ … ⊔ Γ^(k))` for complete context-free
  graphs, equivalently iff `G` admits a faithful context-free action.
- Theorem A (p. 2): for a finitely generated group `G`, `G` embeds in `V` iff
  `G` is `CF-TR`, i.e. admits a faithful context-free action.
- Theorem 2.9 (p. 17): a finitely generated `CF-TR` group
  `G = G(Γ^(1) ⊔ … ⊔ Γ^(k))` is a finitely generated subgroup of `V` (each
  `G(Γ^(i))` embeds in a topological full group of an irreducible edge shift,
  hence in `V`, and `G` embeds in the direct product of the `G(Γ^(i))`).

The claim is exactly the "faithful context-free action ⟹ embeds in `V`"
direction. A faithful action of `G = ⟨A⟩` with orbits `ξ_1·G, …, ξ_k·G`
identifies `G` with the transition group of the disjoint union of the complete
inverse graphs `Sch(ξ_i·G, G; A)`, and `L(ξ_i)` is precisely `L(Γ, ξ_i)`.

Trust boundary: this is a 2026 preprint; the proof of Theorem 2.9 was read at
the level of its structure (it cites [48, Prop. 5.14] and [22, Lemma 4.6] of
that paper, which were not re-verified). An independent proof of the same
characterisation is announced in H. Jaspars, *On context-free subgroups and
R. Thompson's group V*, arXiv:2608.01168v2 (v1 2 Aug 2026, v2 17 Aug 2026);
its abstract (fetched 2026-09-16) states that a group embeds in `V` iff it is
the transition group of a finite union of context-free automata. BDPR's
"Important remark" (p. 4) records the two proofs as independent.
