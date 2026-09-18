---
rg: 2
id: decidable-algebras-embed-in-z2-sft-boundary-product-hosts
kind: claim
title: Every decidable group algebra over F_2 embeds unitally in B_Ω ⊗ L_∂ for some free minimal Z^2-SFT Ω with finitely presented crossed product
distinct_from:
  decidable-group-algebras-have-fp-cantor-crossed-hosts: that allows any torsion-free Farrell–Jones acting group and any Cantor space; this fixes the acting group Z^2 × F_d and the space Ω × ∂F_d with Ω a free minimal Z^2-SFT, and implies that claim.
  free-minimal-z2-sft-is-quantum-rigid: that asks for one quantum rigid free minimal Z^2-SFT over some field; this asks, over F_2, for a family of them whose boundary tensors contain every decidable group algebra.
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem.
Then there are:
- a free minimal `Z^2`-SFT `Ω` over `F_2` with `B_Ω = LC(Ω, F_2) ⋊ Z^2` finitely
  presented;
- some `d >= 2`;
- a unital embedding `F_2[G] -> B_Ω ⊗ (LC(∂F_d, F_2) ⋊ F_d)`.

**Why it matters.** Through
`cantor-crossed-hosts-are-closed-under-boundary-products`, it implies
`decidable-group-algebras-have-fp-cantor-crossed-hosts` (route
`cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts`), and hence
`boone-higman-conjecture` along the graph's chain.

Unlike the bare `Z^2` case (Attempt 2 on the target), a positive answer does
not make `G` linear sofic through a rank model, because the host has none.

**Prerequisites that can fail separately** (artifact Section 4):
- (Q) Existence of one quantum rigid free minimal `Z^2`-SFT over `F_2`. This is the
  `F_2` form of `free-minimal-z2-sft-is-quantum-rigid`.
- (H) The SFTs used must have no uniform recursive language bound. That this is
  necessary is only sketched: it is the table argument of Attempt 6 on the
  target, run over `Z^2 × F_d`.
  - Without freeness and rigidity, hard minimal SFTs exist
    (`minimal-z2-sfts-have-no-uniform-language-time-bound`).
- (E) The embedding.

## Attempts

**Reframing of (E): the boundary factor is only a binary Leavitt factor (swarm-0917, lane w13-bh-pull).**
- `boundary-tensor-hosts-equal-binary-leavitt-tensor-hosts` is ESTABLISHED. For every unital `B` and every `d >= 2`,
  `F_2[G]` embeds unitally in `B ⊗ L_∂(d)` if and only if it embeds unitally in `B ⊗ L_(F_2)(1,2)`.
  - One direction is Brownlowe–Sørensen.
  - The other uses a binary Leavitt family in the corner `e = Σ_(i<d) s_i t_i`, then the augmentation extension.
- So (E) is equivalent to: every decidable `F_2[G]` embeds unitally in `B_Ω ⊗ L_(F_2)(1,2)` for some admissible `Ω`.
  The choice of `d` and the free-group boundary contribute nothing beyond `L(1,2)`.
- This is the container of reduction R2 in the artifact. The boundary factor buys finite presentation of the host
  through Theorem P. It does not buy extra embedding room.

**Consequence for the `Z^4` test case.** A NO for `F_2[Z^4]` would refute (E).
- By corollary (C2) of that claim, the sufficient condition "a corner of `L_∂` contains a Laurent ring in two
  commuting variables" is equivalent to the negation of `leavitt-commuting-units-are-algebraically-dependent`.
  That claim is OPEN, and exact centralizer computations support it.
- So any embedding of `F_2[Z^4]` must use one of three mechanisms, each of which can fail separately:
  - (i) the Leavitt corner. This is equivalent to refuting `leavitt-commuting-units-are-algebraically-dependent`.
    Because of the firewall on that claim, doing so would not decide Ara–Cortiñas Q5.7.
  - (ii) `F_2[Z^3]` in `B_Ω`, or in a corner of it. This is a rank-3 question for crossed products of `Z^2`-SFTs.
    It is the `s = 2` case of the commutative-rank heuristic, under which a `Z^s`-graded Steinberg algebra with an
    AF kernel has no commutative domain of transcendence degree `s + 1`.
  - (iii) an entangled embedding that uses neither tensor factor separately.
- Monomial embeddings are already excluded (the z4 no-monomial-embedding node on the fork branch, not yet in this
  tree).

- A parallel lane (w12-z-pull, the homogeneous Laurent-rank bound for algebraic-core gradings, not in this tree)
  kills two subcases:
  - gauge-homogeneous units in (i);
  - `Z^3`-lattice, gauge-homogeneous and locally PI units in (ii).

  So what survives is inhomogeneous, locally non-PI units.

**Where it stops.** Nothing here constructs or rules out an embedding, so the claim stays OPEN. The next test is
(ii): does any free minimal `Z^2`-SFT crossed product over `F_2` contain `F_2[Z^3]`?
