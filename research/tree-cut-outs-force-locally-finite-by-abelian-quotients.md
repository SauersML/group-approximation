---
rg: 2
id: tree-cut-outs-force-locally-finite-by-abelian-quotients
kind: claim
title: "If a witness is cut out through automorphism groups of s locally finite trees (Aut(T) factors, no host hypothesis at all), every amenable P is virtually (locally finite)-by-Z^k with k <= s; so Grigorchuk's group, BS(1,n), Z wr Z and every torsion-free non-virtually-abelian amenable P are excluded, and a witness for A wr Z (A finite) must have the Diestel-Leader shape: two tree factors in which the shift is hyperbolic with opposite end-orientations, and a nontrivial element of the host whose image fixes pointwise the product of the hulls Y_j of the orbits of the shift axes, on which P acts properly"
distinct_from:
  rank-one-cut-outs-kill-amenable-non-abelian-quotients: That needs AS factors (PGL_2 over local fields), a VSA host and injective subproduct projections, and gets P virtually abelian; this handles Aut(T) factors with non-solvable amenable end stabilizers and no host hypothesis, gets the weaker locally-finite-by-abelian form (which Z/2 wr Z passes), and then pins down the exact shape a Z/2 wr Z witness must take.
  ascending-completions-give-only-virtually-cyclic-quotients: That kills completions with one contracting letter via the parabolic lemma; this uses the same lemma factorwise on end stabilizers of trees to force two opposite-oriented hyperbolic tree factors.
  commensurated-cat0-witnesses-force-finite-rational-cd: That bounds cd_Q P by the complex dimension, which every locally-finite-by-Z^k group passes; this gives a structural (elementary amenable) constraint instead.
---

**ESTABLISHED (proposed, 2026-09-19; referee welcome).** Setting as in
`rank-one-cut-outs-kill-amenable-non-abelian-quotients`: `F` free and
finitely generated, `N ⊴ F`, `P = F/N`, a witness `Σ ≤ Λ`, a homomorphism
`φ : F -> Λ` with `φ^{-1}(Σ) = N`, and `H = φ(F)`, so `P ≅ H/(H ∩ Σ)`.
A **tree cut-out** is a homomorphism
`ρ : Λ -> G = G_1 × ... × G_s`, where each `G_j` is a closed subgroup of
`Aut(T_j)` for a locally finite tree `T_j`, together with a compact open
`K ≤ G` such that `H ∩ Σ = H ∩ ρ^{-1}(K)`. Nothing is assumed about `Λ`
(torsion, finiteness type, discreteness or irreducibility of `ρ(Λ)`).

Write `Ĥ` for the closure of `ρ(H)` and `M = Ĥ ∩ K`. Then `M` is a
compact open normal subgroup of `Ĥ` and `Ĥ/M ≅ P`
(`ascending-completions-give-only-virtually-cyclic-quotients`, item 1).

**Theorem A (amenable quotients).** If `P` is amenable, then `P` has a
subgroup `P'` of index at most `2^s` and a homomorphism `χ : P' -> Z^s`
whose kernel is locally finite. So `P` is virtually
(locally finite)-by-(free abelian of rank `≤ s`).

**Corollaries of A** (every Aut(T)-type cut-out, any host):
1. **Torsion-free `P`.** If `P` is amenable and torsion-free, then `P` is
   virtually `Z^k` with `k ≤ s`. So `BS(1,n)` (`n ≥ 2`), `Z ≀ Z`, the
   Heisenberg group and every non-virtually-abelian torsion-free amenable
   group are excluded.
2. **Torsion `P`.** A finitely generated amenable torsion group `P` is
   realized only if it is finite. So **Grigorchuk's group** and every
   infinite finitely generated amenable torsion group are excluded.
3. **Survivors.** `P` must be (virtually) an extension of a locally finite
   group by `Z^k`. `A ≀ Z` and `A ≀ Z^k` with `A` finite survive this test,
   and they are realized discretely (`M = 1`) on Diestel–Leader graphs
   (`Z/2 ≀ Z` acts freely on `DL(2,2) ⊆ T_3 × T_3`).

**Theorem B (the shape of an `A ≀ Z` witness).** Let `P = A ≀ Z` with `A`
finite and nontrivial (more generally, `P = L ⋊ ⟨t⟩` finitely generated
with `L` locally finite, no nontrivial finite normal subgroup, and
`C_L(t^d) = 1` for all `d ≠ 0`). Suppose a tree cut-out realizes `P`, and
let `τ ∈ Ĥ` lift a power `t^m` lying in `P'`. Then:
1. **Diestel–Leader shape.** `Ĥ` fixes an end `ξ_j` of `T_j` in every
   factor where it has unbounded orbits and is not a pair-of-ends group,
   and among the factors where `τ` is hyperbolic there is one where `τ`
   translates **towards** `ξ_j` and one where it translates **away**.
   In particular `s ≥ 2`, and at least two factors are end-fixing
   (horocyclic) tree factors. Compact and pair-of-ends factors contribute
   nothing to the lamps.
2. **`M` fixes the hull of the axes.** Let `J` be the set of factors where
   `τ` is hyperbolic, `ℓ_j` its axis in `T_j`, and `Y_j` the convex hull of
   `Ĥ·ℓ_j`. Then `M` acts trivially on `∏_{j ∈ J} Y_j`, and the kernel
   `Ker` of `Ĥ` on `∏_{j∈J} Y_j` has `Ker/M` a locally finite normal
   subgroup of `P`. If every factor outside `J` has compact image (e.g.
   `s = |J| = 2`), then `Ker = M` and `P` acts **faithfully and properly**
   on `∏_{j ∈ J} Y_j` (finite vertex stabilizers).
3. **Nontrivial flat fixators.** If `Λ` is torsion-free and `ρ` is injective
   on `H`, then `M` is infinite and `H ∩ Σ` is a nontrivial normal subgroup
   of `H` consisting of elements `λ` with `ρ(λ)` fixing `∏_{j∈J} Y_j`
   pointwise. In particular `Λ` contains `λ ≠ 1` whose image fixes pointwise
   the flat `∏_{j∈J} ℓ_j` of the element `τ₀ ∈ H` (any `τ₀ ∈ H` mapping to
   `t^m` works).

**Corollary B′ (killing criterion).** Let `Λ` be torsion-free and `ρ`
injective on `Λ` (e.g. an irreducible lattice in `G_a × G`, cut out in the
last factors). If no nontrivial element of `Λ` fixes pointwise, under `ρ`,
the product of the axes of an element that is hyperbolic in at least two
tree factors, then no tree cut-out realizes `A ≀ Z` for any finite `A ≠ 1`.
For lattices in products of three trees `T_a × T_b × T_c` cut out in
`(b,c)`, the obstruction group `Λ_F = Λ ∩ (G_a × Fix(ℓ_b × ℓ_c))` is a
free group acting freely on `T_a`, normalized by the element `τ₀`; the
`Aut(T)` case of the Z/2 wr Z question is **equivalent in necessity** to
finding `H ≤ Λ` with `1 ≠ H ∩ Σ ⊆ Λ_F`.

**Sharpness.**
- The literal `DL(2,2)` completion is not reachable nondiscretely: if
  `ρ(H)` acts on `T_3 × T_3` with the `DL(2,2)` orbit hulls
  `Y_b = T_b`, `Y_c = T_c`, item B2 forces `M = 1`, hence `P ≅ H`
  torsion-free by B3, a contradiction. So a nondiscrete witness needs
  `ρ(H)`-hulls that are **proper** subtrees, with the compact part `M`
  living on the hair `T_j ∖ Y_j`.
- Theorem A is attained by `P = Z^s` (flat subgroups of lattices) and, for
  discrete `ρ(H)`, by `A ≀ Z`.

Proof: route `tree-cut-outs-force-locally-finite-by-abelian-quotients-proof`.

## Attempts

- 2026-09-19 (w17-117): Theorems A and B proved. Proposed-established.
  Open: a torsion-free irreducible lattice in three trees with an element
  `τ₀` hyperbolic in `(b,c)`, a nontrivial pointwise flat fixator
  `Λ_F`, and `H ≤ Λ` with `1 ≠ H ∩ Σ ⊆ Λ_F` normal and quotient
  `Z/2 ≀ Z`; or a proof that `Λ_F = 1` for irreducible cocompact lattices
  (which would kill the `Aut(T)` case).
