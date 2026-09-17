---
rg: 2
id: thompson-f-relations-not-finite-hyperfinite-amalgam-trees
kind: claim
title: Amalgamated free products of depth d over amenable subalgebras admit at most d commuting non-amenable subalgebras, so no free pmp orbit relation of Thompson's F is a finite iterated amalgam of hyperfinite relations unless F is amenable
distinct_from:
  thompson-f-lies-in-algebraic-lea-closure-only-if-amenable: that is the group-level closure under extensions, graphs of groups and products; this is the measured / von Neumann level, where tree actions give no contradiction (Gaboriau--Lyons), and the obstruction is Chifan--Houdayer spectral-gap rigidity instead of Bass--Serre theory.
  cordeiro-sofic-relation-permanence: that lists permanence operations that preserve soficity of relations; this shows that finitely many amalgams over hyperfinite subrelations, starting from hyperfinite relations, never reach an orbit relation of a non-amenable F.
  thompson-f-interval-orbit-relation-is-hyperfinite: that is the non-invariant action on [0,1]; this concerns free probability-measure-preserving actions.
  thompson-f-relator-system-stable-in-permutations: that is the open root; this closes the measured amalgam route (Dykema--Kerr--Pichot, Paunescu) left open by the algebraic closure node at finite depth, and names directed unions and products as its survivors.
---

**ESTABLISHED (unreviewed).** Proof:
`thompson-f-relations-not-finite-hyperfinite-amalgam-trees-proof`.

**Depth classes.** Every von Neumann algebra below is finite and carries a faithful normal trace.
- `𝒜_0` is the class of amenable finite von Neumann algebras.
- `𝒜_(d+1)` is the class of amalgamated free products `N_1 *_B N_2`, where `N_1, N_2 ∈ 𝒜_d`, `B` is
  amenable, and the traces agree on `B`.
- Since `N *_B B = N`, the classes increase: `𝒜_d ⊆ 𝒜_(d+1)`.

For a finite von Neumann algebra `M`, the **commuting depth** `κ(M)` is the supremum of all `k` such that
some corner `qMq` (`q ≠ 0`) contains `k` pairwise commuting unital von Neumann subalgebras
`P_1, …, P_k`, none of which has an amenable direct summand.

**Theorem.**
1. **Depth bound.** If `N ∈ 𝒜_d`, then `κ(N) ≤ d`.
2. **Thompson's F.** Suppose `F` is not amenable.
   - Take disjoint dyadic intervals `I_1, …, I_k`. The factors `L(F_(I_j)) ≅ L(F)` pairwise commute and
     are non-amenable, so `κ(L(F)) = ∞`.
   - This persists in every tracial von Neumann algebra containing `L(F)` unitally, for instance
     `L^∞(X) ⋊ F`. So `L^∞(X) ⋊ F ∉ ∪_d 𝒜_d` for every trace-preserving action.
3. **Relations.**
   - `ℛ_0` is the class of hyperfinite pmp equivalence relations.
   - `ℛ_(d+1)` is the class of relations `R_1 *_(R_0) R_2`, amalgamated in Gaboriau's sense, with
     `R_1, R_2 ∈ ℛ_d` and `R_0` hyperfinite.
   - **Dichotomy.** A free pmp orbit relation of `F` lies in `∪_d ℛ_d` exactly when `F` is amenable.
   - In particular it is not a finitely generated treeable relation, nor a finite tree of hyperfinite
     relations over hyperfinite edge relations.
4. **Localization.** Take any decomposition `R_F = R_1 *_(R_0) R_2` with `R_0` hyperfinite and pieces
   arbitrary. For all `k`, some piece `R_i` receives a normal injective `*`-homomorphism
   `L(F^k) → pM_n(L(R_i))p` that intertwines inside `L(R_F)`.
   - Every such splitting therefore pushes a copy of `L(F^k)` into one piece, for every `k`.
   - Soficity of that piece is at least as hard, at the von Neumann level, as the question for `F^k`.

**Reading for the root.**
- **What this closes.** Dykema--Kerr--Pichot and Păunescu make `R_1 *_(R_0) R_2` sofic when the pieces
  are sofic and `R_0` is hyperfinite. Iterating finitely many times from hyperfinite relations cannot give
  an orbit relation of a non-amenable `F`, and hence cannot give separating almost-solutions for the root
  through Elek--Lippner.
- **What survives.**
  - Directed unions of finite-depth relations (Cordeiro: increasing unions of sofic relations are sofic).
    `κ` is not upper semicontinuous under unions.
  - Products of relations: `L(F)` is McDuff (Jolissaint), so tensor primality is not available.
  - HNN-type splittings over hyperfinite subrelations. The Ueda corner trick should reduce these to
    amalgams, but it is not checked here.
- **Not F-specific beyond `κ = ∞`.** The sofic group `⊕_N F_2` also has infinite commuting depth. The
  theorem excludes a *mechanism*, not soficity. This calibrates the obstruction: it can never alone refute
  the root.

**Calibration.**
- `F_2 × Z = (Z×Z) *_Z (Z×Z)` lies in `𝒜_1`, and `κ = 1`.
- `κ(L(F_2 × F_2)) ≥ 2`, so `L(F_2×F_2) ∉ 𝒜_1`, in line with Chifan--Houdayer primeness.
- The group-level analogue holds by Bass--Serre theory. In an amalgam over amenable edge groups, the
  centralizer of a non-elementary subgroup lies in an edge stabilizer.
