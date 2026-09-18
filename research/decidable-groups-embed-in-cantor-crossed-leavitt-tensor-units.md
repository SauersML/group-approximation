---
rg: 2
id: decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units
kind: claim
title: Every decidable group embeds in the unit group of B ⊗ L for some finitely presented central simple Cantor crossed product B over a torsion-free Farrell–Jones group
distinct_from:
  decidable-group-algebras-have-fp-cantor-crossed-hosts: that asks for a unital embedding of the group algebra F_2[G] into B itself; this asks only for an injective homomorphism of G into (B ⊗ L)^x, which may use GL_n(B) and Leavitt isometries, and is implied by that claim.
  simple-inputs-have-fp-elementary-leavitt-tensor-hosts: that embeds a simple input group into B^x for elementary hosts; this allows any decidable G and any unit of the Leavitt tensor, for crossed-product hosts.
  decidable-group-algebras-have-fp-central-simple-hosts: that is the ring-level host existence with a K-theory condition; this is group-level and restricts to crossed products, where the K-theory condition is automatic.
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
---

**OPEN.** Let `G` be a finitely generated group with solvable word problem, and
let `L = L_(F_2)(1,2)`. Then there are:
- a torsion-free group `P` satisfying the `K`-theoretic Farrell–Jones conjecture
  with additive categories as coefficients, with respect to `VCyc`;
- a nonempty compact totally disconnected Hausdorff `P`-space `X` such that
  `B = LC(X, F_2) ⋊ P` is finitely presented, simple, and has centre `F_2`;
- an injective group homomorphism `G -> (B ⊗ L)^x`.

**Why it matters.**
- It implies `boone-higman-conjecture` by route
  `boone-higman-via-units-of-cantor-crossed-leavitt-tensors`, along the same
  chain as the target (conditional on Khanh arXiv:2609.08428v1).
- It is implied by `decidable-group-algebras-have-fp-cantor-crossed-hosts`,
  through `G <= F_2[G]^x <= B^x <= (B ⊗ L)^x`.
- It asks for strictly less algebraic structure. `G` need not span a copy of
  `F_2[G]`, and it may use `GL_n(B) ⊆ GL_1(M_n(B) ⊗ L)`, since `M_n(L) ≅ L`, as
  well as Thompson-like units built from the Leavitt isometries.
- Over boundary products (`cantor-crossed-hosts-are-closed-under-boundary-products`),
  `B ⊗ L_∂ ⊗ L` is again of this shape.

For a fixed host, the question is embeddability into one finitely presented
simple group. The family must still have unbounded word-problem complexity
(`complexity-bounded-host-classes-are-not-universal`).

## Attempts

1. **2026-09-18 (swarm-0917-w10-w10-bh-last1, logic-computability): does the
   Leavitt factor buy complexity?** No. Recorded as the class kill
   `free-group-leavitt-tensor-units-are-not-universal`
   (ESTABLISHED, unreviewed), through the transfer lemma
   `leavitt-tensor-unit-word-problem-reduces-to-base` (ESTABLISHED, elementary).
   - **Lemma.** Every finitely generated subgroup of `GL_N(B ⊗ L)` has word
     problem in time `C 2^(Cl)(1 + F_B(C 2^(Cl)))`, where `F_B` is the zero test
     of `B`. Reduce Leavitt monomials to `x_α x_β^*`, pad every `β` to one length
     `n` with `Σ_(|γ|=n) x_γ x_γ^* = 1`, and read off `B`-coefficients against the
     independent family `{x_α x_β^* : |β| = n}` in each degree.
   - **Kill.** `P` free dies, including `P = Z` and `P = 1`, whatever `X`, for
     units, matrices and Leavitt isometries alike. Named invariant: the local
     extension property of tree SFTs, which gives a doubly exponential zero test
     for `B`. Since `P` must be torsion-free, this is the whole virtually free
     class. It is the units-level twin of Attempt 4 on
     `decidable-group-algebras-have-fp-cantor-crossed-hosts`.
   - **What transfers in general.** Every kill of the group-algebra form that
     runs through a uniform zero-test bound for a family of bases `B` now kills
     this claim over the same family. The constraints that concern `B` alone
     transfer verbatim: `X` an SFT (`fp-crossed-products-force-sft-over-any-group`),
     `P` finitely presented, `P` not free.
   - **What does not transfer.** The growth-counting kill on the group-algebra
     form uses that `F_2[G]` spans. Here `G` may sit on Thompson-like units of
     `L`, which already contain `V` and nonabelian free groups, so no growth
     comparison with `B` is available.
   - **Where the claim now stands.** A proof must use a non-free, finitely
     presented, torsion-free Farrell–Jones `P` and an SFT `X` whose zero test
     has no recursive bound uniform over the family used. The Leavitt tensor
     contributes K-theory and simplicity, never complexity. So the input's
     word problem must be encoded in the pattern language of `X`. Stays OPEN.
