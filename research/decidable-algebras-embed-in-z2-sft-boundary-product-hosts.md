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

**Attempt (faithful point column transplant, swarm-0917-w14; OPEN).** This transplants the
probability/random-walk habit of reading an operator through one random starting point to the regular
representation of the host. The result is `steinberg-ore-domains-have-faithful-point-columns`, ESTABLISHED
(unreviewed) with a self-contained route.

- **Lemma.** A nonzero left Ore domain `C` inside `LC(X, k) ⋊ P`, or inside any ample groupoid algebra with
  compact unit space, acts faithfully on the column of one point `x`. That is, `c |-> π_x(c) δ_e` is
  injective.
- **Proof idea.** The points killed by a nonzero `c` form a clopen set. Compactness plus the Ore condition
  produce one nonzero `h` killing every column. The columns separate elements, so `h = 0`.
- **Where it applies.**
  - `dim V_n <= |B_P(mn)|` for Ore inputs, with no pattern count factor.
  - So `B_Ω` alone, and every crossed product over a virtually nilpotent group of growth degree `D`, contains
    no `F_2[Z^(D+1)]`, whatever the space. This includes exponential-complexity free minimal SFTs.
  - The boundary factor is therefore needed for the input `Z^3` for every choice of `Ω`, not only for slow
    `Ω`.
- **Where it dies on (E).**
  - Here `P = Z^2 × F_d`, and the orbit balls `B_P(mn)` grow exponentially. The count is vacuous at every
    Ore input.
  - What survives is the structural fact: any unital `F_2[Z^4] ⊆ B_Ω ⊗ L_∂` acts faithfully on a single
    column `k^(Z^2 × F_d)` at some point `(ω, ξ)`, with the degree-`n` part supported on
    `B_(Z^2)(mn) × B_(F_d)(mn)`.
  - Turning this into a NO for `Z^4` requires a linear analog of the monomial tree-slab argument on that
    column. Such an analog would also have to exclude `F_2[Z^2] ⊆ L(1,2)`, and so decide the direction
    of `leavitt-commuting-units-are-algebraically-dependent`. The reason:
    - `F_2[Z^2] ⊆ B_Ω` through the `v_p`, and tensor products of injective maps over a field are
      injective.
    - So `F_2[Z^2] ⊆ L(1,2)` would give `F_2[Z^4] ⊆ B_Ω ⊗ L(1,2)`.
    - By the swarm's binary-Leavitt reduction, that is the same as an embedding in `B_Ω ⊗ L_∂`. That exclusion is the `F_2` shadow of Ara–Cortiñas Question 5.7
    (arXiv:1108.0352v3, p. 8), which is open.
  - So the attempt stops at that firewall.
- **Status.** (E) stays OPEN.
