---
rg: 2
id: local-passivity-without-no-creation-is-gottschalk-proof
kind: route
title: Constant-fixing powers satisfy centre fixing automatically, and rest-patch preservation already makes the finite pieces invariant
target: local-passivity-without-no-creation-is-gottschalk
requires:
  - local-passivity-preserving-injective-automata-are-surjective
---

Complete direct proof. Notation as in the target. Convention: `τ(x)(g) = f((g⁻¹x)|_M)` for a memory `M` and local
rule `f`.

**Part A.**
1. **Powers fix constants.** An automaton maps constant configurations to constant configurations. If `τ` is
   injective, it permutes the finite set of constant configurations, so some `τ^k` fixes all of them, in particular
   `a^G`.
2. **The power is strict.** `τ^k` is injective. Its image is contained in `τ(A^G)`, which is a proper subset, so
   `τ^k` is not surjective. Let `M_k` be a memory of `τ^k`, with local rule `f_k`.
3. **(1) holds.** Let `W ⊇ M_k ∪ {1}` and `P = {a^W}`. If `g ∉ Act(x)` then `x = a` on `gW ⊇ gM_k`, so
   `τ^k(x)(g) = f_k(a^(M_k)) = τ^k(a^G)(g) = a = x(g)`.
4. **Equivalence.** If `G` is not surjunctive, steps 1 to 3 give an injective, non-surjective automaton satisfying
   (1) for `P = {a^W}`. Conversely, if `G` is surjunctive, every injective automaton is surjective, with or without (1).

**Part B.** Let `P = {a^W}`, so `Act(x) = { g : x ≠ a somewhere on gW }`.
1. **(2) implies (1).** If `g ∉ Act(x)` then `x = a` on `gW`. By (2), `g ∉ Act(Φ(x))`, so `Φ(x) = a` on `gW`. Since
   `1 ∈ W`, `Φ(x)(g) = a = x(g)`.
2. **Surjectivity.** Apply `local-passivity-preserving-injective-automata-are-surjective`. For the record, the pieces
   are finite directly: if `Act(z) ⊆ E` then `z(g) = a` for every `g ∉ E` (take `w = 1`), so
   `D_E = { z : Act(z) ⊆ E }` has at most `|A|^|E|` elements. By (2), `Φ` maps `D_E` into itself, hence onto it.
   Every configuration equal to `a` off a finite set `F` lies in `D_(F W⁻¹)`, and these configurations are dense.
   The image is closed, so `Φ` is surjective.
3. **Where non-rest symbols may appear.** If `Φ(x)(h) ≠ a`, then by (2) no `g ∈ hW⁻¹` has `x = a` on `gW`. Taking
   `g = h`, the patch `hW` meets the support `{x ≠ a}`, so `h ∈ {x ≠ a} W⁻¹`.

**Part C.** With `P = A^W` every pattern is passive, so `Act(x) = ∅` for all `x` and (2) holds for every automaton. The
statement "(2) implies surjective" is then surjunctivity of `G`.

**Calibration.**
- **Amenable and sofic groups.** Part A says (1) alone gives surjectivity there, consistent with the Garden of Eden
  theorem and Gromov–Weiss.
- **The shift on `{0,1}^Z`** fixes `0^Z` and has memory `{1}`, so it satisfies (1) for `W = {0, 1}` and `P = {00}`.
  It is bijective, consistent with both parts. It violates (2): on `x = δ_1` the patch `{0, 1}` is not at rest in `x`,
  but at `g = -1` the patch `{-1, 0}` is at rest in `x` and not in `σ(x) = δ_0`.
- **The rule "a site becomes `1` if a neighbour is `1`"** on `{0,1}^Z` fixes `0^Z`, satisfies (1) for `W ⊇ {-1,0,1}`,
  and is not injective: `1_{0,2}` and `1_{0,1,2}` are both sent to `1_{-1,0,1,2,3}`. This is consistent with A, which
  asserts nothing about non-injective rules.
