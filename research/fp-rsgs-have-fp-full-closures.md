---
rg: 2
id: fp-rsgs-have-fp-full-closures
kind: claim
title: Every finitely presented rational similarity group has a finitely presented full closure (BBMZ-hyperbolic Question 1.4)
distinct_from:
  contracting-rsgs-embed-in-fp-simple-groups: that imports Theorem B, finite presentation of FULL contracting RSGs; this asks whether finite presentation of an arbitrary RSG passes to its full closure, with no contracting hypothesis.
  contracting-rsgs-have-fp-full-closures: that settles the contracting case of this question; this is the question itself.
  fp-clopen-transitive-full-cantor-groups-have-type-a-actions: that turns a finitely presented FULL Cantor group into a type (A) actor; this asks when fullness can be added without losing finite presentation.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**OPEN.**

**The printed question.** Belk--Bleak--Matucci--Zaremsky, *Hyperbolic groups satisfy the
Boone--Higman conjecture*, arXiv:2309.06224, TeX source line 236 (local copy
`$GQ/src/bh-free-03/bbmz2-2309.06224.tex`), verbatim:

> "If $G$ is a finitely presented RSG, then must the full closure of $G$ also be finitely presented?"

The preceding sentence (line 233) motivates it by Scott's theorem that the
Röver--Nekrashevych group `V_d(G)` of a finitely presented self-similar group `G` is
finitely presented (and Skipper--Witzel--Zaremsky's higher version).

**Terms** (BBMZ, as quoted in `contracting-rsgs-embed-in-fp-simple-groups`). `Σ_Γ` is the
edge shift of a finite graph, `R_{Γ,E}` the group of rational homeomorphisms of a nonempty
clopen `E` (finitely many local actions). An RSG is a subgroup `G ≤ R_{Γ,E}` that realizes
the canonical similarity between any two proper cones with the same terminal vertex. The
full closure `[[G]]` is the group of homeomorphisms of `E` that locally agree with `G`.
`G` is contracting if `Σ_Γ` has an irreducible core and the nucleus `N_G` (local actions
occurring infinitely often, over `g ∈ G`) is finite.

**Why it matters for Boone--Higman.** A finitely presented full clopen-transitive Cantor
group is a type (A) actor (`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`).
So a positive answer turns every finitely presented RSG into a type (A) host. That is the
Cantor-host gap between `decidable-groups-embed-in-fp-locally-moving-groups` and
`boone-higman-conjecture`, restricted to rational hosts.

## Known cases

- **Contracting inputs:** yes, by `contracting-rsgs-have-fp-full-closures` (BBMZ Theorem B
  applied to `[[G]]`). So any counterexample is non-contracting.
- **Full inputs:** trivially yes (`[[G]] = G`). This covers Röver--Nekrashevych groups of
  finite-state self-similar groups, which BBMZ note are full RSGs (TeX line 657).
- **The first open family:** `v-normalizer-rsgs-contract-iff-finite-outer-order`. For every
  homeomorphism `t` normalizing Thompson's `V` whose class in `Out(V)` has infinite order,
  `Γ_t = ⟨V, t⟩ = V ⋊ ⟨t⟩` is a finitely presented, non-contracting, non-full RSG. For order
  at least 3 its core is asynchronous
  (`synchronous-cores-in-out-v-have-order-at-most-two`), so neither Theorem B nor the
  synchronous Scott/Skipper--Witzel--Zaremsky theory applies to `[[Γ_t]]`. The family was
  first noted in bh-free-23's artifact, without claims.

## Attempts

1. **The germ groupoid of the test family (bh-higman-classic, 2026-09-18).** *Reduction, not decided.*
   - **The groupoid.** Take `t` of infinite order in `Out(V)`. By
     [[v-normalizer-groupoids-carry-lag-cocycle-iff-lipschitz]], `[[Γ_t]]` is the topological full group
     of `O ⋊_t Z`, and the lag cocycle extends iff `t` is Lipschitz.
   - **The Lipschitz case** (`t ∈ L_2 ≅ Inert(σ_2)`). The groupoid is Z-graded: a "rank-two Cuntz"
     groupoid built from the commuting pair `(σ, F)` of the full 2-shift and an inert `F`. That is the
     nearest known shape to the `k`-graph groupoids whose full groups X. Li proves are of type `F_∞`
     (`li-finite-k-graph-full-groups-are-f-infinity`).
   - **Why Li does not apply as stated.**
     - His self-similar and Zappa–Szép cases need a degree-preserving action.
     - An inert `F` of infinite order is intrinsically asynchronous
       ([[synchronous-cores-in-out-v-have-order-at-most-two]]).
     - Recoding by higher blocks makes `F` causal, but `F^{-1}` then still needs lookahead. Only one-sided
       automorphisms (the identity and the flip) are causal both ways.
   - **No homological obstruction expected (heuristic).** A Wang-type exact sequence for `O ⋊ Z`, together
     with `H_*(O_2) = 0`, would give `H_*(G_t) = 0`. That sequence was not checked at source.
   - **Next.** Either (a) a Garside or Stein–Farley complex for `[[Γ_t]]` built from the lag grading
     (Lipschitz case), or (b) an obstruction for non-Lipschitz `t`, where no Z-grading exists.
