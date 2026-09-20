---
rg: 2
id: zaremsky-1-06-by-level-zero-dead-cut-laplacian
kind: route
title: "Zaremsky Problem 1.6 answered by the level-0 dead-cut Laplacian: Sigma^1(A_Gamma) is the union of the type cells whose level-0 Laplacian over Z[ker chi] is onto"
target: zaremsky-1-06-bns-invariant-of-every-artin-group
requires:
  - artin-sigma1-equals-dead-cut-laplacian-surjectivity
  - artin-sigma1-is-level-zero-laplacian-surjectivity
  - artin-level-zero-laplacian-surjectivity-is-decidable
---

This route replaces the dead route `zaremsky-1-06-by-living-subgraph-formula`, whose only
prerequisite is refuted.

**The answer it gives.** For every Artin group `A_Γ`, `Σ^1(A_Γ)` is the union of the type
cells `C_τ` (sign vector and set of edges with `χ(u) + χ(v) = 0`) such that:
1. `τ` is dominant: every vertex of sign `0` has a neighbour of nonzero sign;
2. the level-0 Laplacian `L_0(τ)` is onto `K_r(Z[H'_τ])`.

There are finitely many types for each `Γ`.

**Three prerequisites. Each can fail on its own.**
1. `artin-sigma1-equals-dead-cut-laplacian-surjectivity` (ESTABLISHED, unreviewed).
   - It gives the exact Novikov criterion.
   - It proves that `L_0` onto implies membership.
   - It proves that `L_0`-surjectivity depends only on the type.
   - *How it could fail:* an error in the elimination. The numerics cover 400 + 400 random
     graphs with dead vertices, dead edges and nonzero `H_1`.
2. `artin-sigma1-is-level-zero-laplacian-surjectivity` (OPEN). The converse: Novikov
   surjectivity descends to level `0`.
   - *How it could fail:* a type cell that contains characters on both sides. Another way is
     `L_0(χ)` onto but `L_0(-χ)` not onto, which would contradict `Σ^1 = -Σ^1`.
   - It can fail even if (3) holds, since (3) says nothing about `Σ^1`.
3. `artin-level-zero-laplacian-surjectivity-is-decidable` (OPEN). An effective test for the
   finite list of unimodularity questions over `Z[H'_τ]`.
   - *How it could fail:* group-ring word or membership problems in the subgroups
     `H'_τ ≤ A_Γ` are undecidable. That is independent of (2).
   - If (3) fails but (1) and (2) hold, the answer is still an exact criterion, just not an
     algorithm.

**Why this is the right decomposition.**
- (1) isolates everything that is pure bookkeeping in the Fox calculus.
- (2) is the only place where Novikov analysis, with negative levels, enters.
- (3) is a pure question about group rings.
- The known families sit inside it:
  - Meier: `r = 1`;
  - the prime-`p` family and `A(3,4,6)`: `L_0` not onto, by augmentation and by a ring
    witness;
  - `K_q` odd and the mixed `K`: explicit identities.
