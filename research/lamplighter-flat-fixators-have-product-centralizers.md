---
rg: 2
id: lamplighter-flat-fixators-have-product-centralizers
kind: claim
title: "In a torsion-free cocompact three-tree lattice, the flat fixator Λ_F of an element hyperbolic in all three trees is never trivial (so the Λ_F = 1 kill of Corollary B′ never applies to a cocompact host), while every nontrivial element n of a lamplighter cut-out's flat fixator N has centralizer commensurable to C_0 × ⟨n⟩ with C_0 non-amenable and acting geometrically on Fix_b(n) × Fix_c(n), two infinitely-ended trees; hosts with amenable centralizers (all arithmetic ones) are killed, and for one-vertex cube lattices the condition is an exact finite-state test on a-words"
distinct_from:
  lamplighter-cut-outs-act-freely-on-the-third-tree: That shows H acts freely on T_a and kills hosts with a discrete cut-out projection; this computes the centralizer of each element of N in the host (flat torus / centralizer theorem) and shows the Λ_F = 1 route proposed there is empty for all cocompact hosts.
  tree-cut-outs-force-locally-finite-by-abelian-quotients: That produces N and its fixed hulls Y_b, Y_c and states the Λ_F = 1 killing criterion; this shows that criterion never fires for cocompact hosts and replaces it with a centralizer criterion that does.
  linear-dl-factor-kills-lamplighter-tree-cut-outs: That kills hosts with a linear PGL_2 factor using linear algebra; this kills every host whose centralizers are amenable, with no linearity, and recovers the arithmetic case as a special case.
---

**ESTABLISHED (proposed, 2026-09-19; referee welcome).** Setting of
`lamplighter-cut-outs-act-freely-on-the-third-tree`, with `Λ` in addition
**cocompact**. So `Λ` is a torsion-free cocompact lattice in
`G_a × G_b × G_c` (closed `G_j ≤ Aut(T_j)`, locally finite trees), cut out
in `(b, c)` with `ρ = pr_{bc}` injective on `H`, `Σ = Λ ∩ ρ^{-1}(K)`,
`N = H ∩ Σ` and `P = H/N = A ≀ Z` (`A` finite nontrivial). For `τ`
hyperbolic in `b` and `c` with axes `ℓ_b, ℓ_c`, write
`Λ_F(τ) = Λ ∩ (G_a × Fix(ℓ_b × ℓ_c))`.

**Theorem F (flat fixators are never trivial).**
1. If `τ ∈ Λ` is hyperbolic in all three trees, then `Λ_F(τ)` contains an
   element `λ₀ ≠ 1` that commutes with `τ` and translates `ℓ_a(τ)`.
2. If `τ` is elliptic in `a`, then `Λ_F(τ)` is the increasing union of the
   groups `C_{Λ_F(τ)}(τ^{D!})`. Each of these acts freely and cocompactly on
   the subtree `Fix_{T_a}(τ^{D!})`. So `Λ_F(τ) ≠ 1` iff some `Fix_{T_a}(τ^D)`
   is unbounded, and `Λ_F(τ)` is non-abelian iff some `Fix_{T_a}(τ^D)` has
   at least three ends.
3. Every `τ₀ ∈ H∖1` is hyperbolic in `a` (Theorem E2), so case 1 applies to
   the flat of the shift. **Corollary B′ never applies to a cocompact
   host**, and the "certify `Λ_F = 1`" step proposed for this target is
   impossible for every host: Rattaggi, Kimberley–Robertson, Burger–Mozes
   and arithmetic alike.

**Theorem W (product centralizers).** Let `n ∈ N∖1`.
1. `n` is hyperbolic in `a` (E2). Its fixed trees `Fix_b(n) ⊇ Y_b` and
   `Fix_c(n) ⊇ Y_c` each have **infinitely many ends**: `Y_j` is leafless
   and is not a line, because otherwise the lamps would have infinite
   vertex stabilizers in `P`'s proper action on `Y_b × Y_c`.
2. `C_Λ(n)` acts cocompactly on `Min(n) = ℓ_a(n) × Fix_b(n) × Fix_c(n)`.
   A finite-index subgroup `C′` translates `ℓ_a(n)`. The kernel `C_0` of the
   translation character fixes `ℓ_a(n)` pointwise and acts freely and
   cocompactly on `Fix_b(n) × Fix_c(n)`. Also `C_0 × ⟨n⟩` has finite index
   in `C_Λ(n)`.
3. `C_0` is **non-amenable**. It has exponential growth, so the
   Sageev–Wise Tits alternative for cube complexes gives `F_2 ≤ C_0`. So
   `Λ ⊇ F_2 × ⟨n⟩`, with the `Z` factor inside `N`.

**Corollary W1 (centralizer kill).** No cut-out of `A ≀ Z` exists in a
torsion-free cocompact three-tree lattice `Λ` if either:
- every nontrivial element of `Λ` that is hyperbolic in exactly one tree
  has an amenable centralizer; or
- every `λ ∈ Λ∖1` that is elliptic in `b` fixes a subtree of `T_b` with
  finitely many ends. In particular this forces `pr_b` to be injective on
  `Λ`. The same condition with `c` in place of `b` also suffices.

This covers every `S`-arithmetic quaternionic host, since its centralizers
are tori, recovering Corollary 1 of the linear-DL node without
linear-algebraic input. It also covers every host whose projections have
the property that nontrivial elliptic elements fix subtrees with at most
two ends.

**Corollary W2 (exact finite-state test for cube lattices).** Suppose `Λ`
acts simply transitively on the vertices of `T_a × T_b × T_c`: a one-vertex
cube complex with letter sets `A, B, C`, VH-structures and the cube
condition. If `Λ` has a cut-out of `A ≀ Z`, then:
- some cyclically reduced `a`-word `w ≠ 1` is **doubly branching**:
  `Fix_b(w)` and `Fix_c(w)` both have infinitely many ends;
- `w` commutes with a non-amenable subgroup of `⟨B ∪ C⟩`.

For each `w`, `Fix_b(w)` is the language of a finite automaton. Its states
are the `a`-words of length `|w|` produced by pushing `w` through
`B`-letters. Infinitely many ends is decided exactly: some reachable node of
the pruned automaton lies on a cycle and has out-degree at least 2. See
`experiments/lamplighter-flat-fixators-2026-09-17/branching.py`. Words
failing the test are certified not to lie in any `N`.

**Calibration (computed).** The experiments directory has a SAT generator
for one-vertex cube complexes (`cubesat.py`), a normal-form associativity
check (`irred.py`) and the exact end test.
- All six of the `(4,4,4)` and `(6,6,6)` complexes tested are reducible in
  some direction, meaning a level-1 action equals its level-2 action.
- These complexes all have doubly branching `a`-words, which is expected
  when a factor acts virtually trivially. Such hosts are killed by E3.1
  anyway.
- No complex found was irreducible in all six directions. This covers the
  61 no-commute `(4,4,4)` complexes enumerated and 13 randomized
  `(4,6,8)` and `(6,6,6)` draws. Most random-assumption draws were
  infeasible, and the level-1-transitive variants had no solutions within
  the search budget.
- **So the test has not been run on a genuinely irreducible host.**

**Open (the one remaining host class).** Determine whether an irreducible
torsion-free cocompact lattice in a product of three trees can contain
`n ≠ 1`, hyperbolic in `a`, whose centralizer is `C_0 × ⟨n⟩` with `C_0` a
non-amenable lattice in `Aut(Fix_b(n)) × Aut(Fix_c(n))`. There are two ways
forward:
- **Prove "no".** Irreducible hosts have amenable centralizers, which closes
  the `Aut(T)` three-tree case of the target.
- **Find "yes"**, via a doubly branching `a`-word in a Rattaggi-type
  irreducible cube lattice. Then check the Schottky and core conditions of
  E2/E3.2 on `⟨C_0, w⟩`.

Proof: route `lamplighter-flat-fixators-have-product-centralizers-proof`.

## Attempts

- 2026-09-19 (w20-117): Theorems F, W and W1–W2 proved (proposed-established).
  Exact test implemented. Calibration on reducible complexes done. No
  irreducible one-vertex three-tree complex was found at small degrees.
