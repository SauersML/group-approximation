---
rg: 2
id: boundary-tensor-hosts-equal-binary-leavitt-tensor-hosts
kind: claim
title: A group algebra embeds unitally in B ⊗ (LC(∂F_d, F) ⋊ F_d) if and only if it embeds unitally in B ⊗ L_F(1,2), for every field F, unital algebra B and d >= 2
distinct_from:
  cantor-crossed-hosts-are-closed-under-boundary-products: that shows B ⊗ L_∂ is again a finitely presented Cantor crossed product host; this shows that, for group-algebra embeddings, the boundary factor can be swapped for the binary Leavitt algebra in both directions, and that d is irrelevant.
  countable-graph-leavitt-path-algebras-embed-in-binary-leavitt: that is the Brownlowe–Sørensen embedding L(E) -> L(1,2), one direction only; this adds the converse for group algebras through a Leavitt corner of the boundary crossed product and the augmentation extension.
  leavitt-commuting-units-are-algebraically-dependent: that is the open statement that F_2[Z^2] has no unital embedding in L_(F_2)(1,2); by the case B = F_2 here, it is equivalent to saying that no corner of any boundary crossed product contains a two-variable Laurent ring.
  decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units: that asks for a group embedding into units of B ⊗ L(1,2) over a Farrell–Jones actor; this is an exact transfer lemma between two kinds of tensor host.
---

**ESTABLISHED** by `boundary-tensor-hosts-equal-binary-leavitt-tensor-hosts-proof`.

Let `F` be a field, `B` a unital `F`-algebra, `d >= 2`, and
`L_∂(d) = LC(∂F_d, F) ⋊ F_d`. Put `L = L_F(1,2)`. For every group `G` these are equivalent:
1. there is a unital injective algebra map `F[G] -> B ⊗ L_∂(d)`;
2. there is a unital injective algebra map `F[G] -> B ⊗ L`.

In particular, condition 1 does not depend on `d`.

The only special feature of `F[G]` that is used is its augmentation `ε : F[G] -> F`. The same statement holds for any
augmented unital `F`-algebra in place of `F[G]`.

## Corollaries

**(C1) Reformulation of (E).** Take `F = F_2` and `B = B_Ω = LC(Ω, F_2) ⋊ Z^2`. Then the embedding prerequisite (E)
of `decidable-algebras-embed-in-z2-sft-boundary-product-hosts` is equivalent to the following: for every finitely
generated `G` with solvable word problem, there is a free minimal `Z^2`-SFT `Ω` with `B_Ω` finitely presented and a
unital embedding `F_2[G] -> B_Ω ⊗ L_(F_2)(1,2)`.
- The boundary factor and `d` play no role.
- The container `B_Ω ⊗ L(1,2)` is the one that appears in reduction R2 of
  `research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md`.

**(C2) Corner mechanism.** Take `B = F` and `G = Z^2` over `F = F_2`. The following are equivalent:
- some nonzero corner `e L_∂(d) e` contains two commuting units `u, v` of `e L_∂(d) e` that satisfy no nonzero
  Laurent relation;
- `F_2[Z^2]` embeds unitally in `L_∂(d)`;
- `F_2[Z^2]` embeds unitally in `L_(F_2)(1,2)`, which means `leavitt-commuting-units-are-algebraically-dependent`
  is false.

The same holds with `Z^2` replaced by any group `G`.

**Consequence for the `Z^4` fork.** The `Z^4` test case (`F_2[Z^4]` in `B_Ω ⊗ L_∂`) is recorded on the target's
Attempts. Its sufficient condition, "a corner of `L_∂` contains a Laurent ring in two commuting variables", is exactly
the negation of an open, well-evidenced claim. Because of the firewall on that claim, it would also not settle
Ara–Cortiñas Question 5.7.
