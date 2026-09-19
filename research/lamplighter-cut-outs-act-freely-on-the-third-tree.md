---
rg: 2
id: lamplighter-cut-outs-act-freely-on-the-third-tree
kind: claim
title: "In a three-tree lattice cut-out of A wr Z (Λ torsion-free discrete in G_a × G_b × G_c, cut out in (b,c), ρ injective on H), every element of H normalizing the flat fixator N = H ∩ Σ that is elliptic on T_a would have finite N-conjugation orbits, which forces its image in P to centralize L; so H acts freely on T_a and is a finitely generated free Schottky group, N is infinitely generated for every infinite P; a host whose Σ-core over H has finite index in Σ, or with one cut-out projection discrete on H, is killed"
distinct_from:
  linear-dl-factor-kills-lamplighter-tree-cut-outs: That kills hosts with one linear PGL_2 DL factor and shows only that the lamp preimage H_L acts freely on T_a; this needs no linearity and shows the whole of H acts freely on T_a (so H is free), via a discreteness/finite-orbit argument in the third tree.
  tree-cut-outs-force-locally-finite-by-abelian-quotients: That gives the Diestel-Leader shape and the flat fixator; this uses both to constrain the host lattice through its third (uncut) factor.
---

**ESTABLISHED (proposed, 2026-09-19; referee welcome).** Setting of
Theorem D of `linear-dl-factor-kills-lamplighter-tree-cut-outs`: `Λ` a
torsion-free discrete subgroup of `G_a × G_b × G_c` (closed
`G_j ≤ Aut(T_j)`, locally finite trees), cut out in `(b, c)` with
`ρ = pr_{bc}` injective on `H`, compact open `K ≤ G_b × G_c`,
`Σ = Λ ∩ ρ^{-1}(K)`, `N = H ∩ Σ`, `P = H/N = A ≀ Z` with `A` finite
nontrivial (more generally `P = L ⋊ ⟨t⟩` as in Theorem B with
`C_L(γ) = 1` for every `γ ∈ P ∖ L`; this holds for every `A ≀ Z`).
`H_L` is the preimage of `L`.

**Theorem E1 (finite-orbit lemma).** If `g ∈ Λ` normalizes `N` and
`pr_a(g)` fixes a vertex of `T_a`, then every `n ∈ N` has a finite orbit
under conjugation by `g`; so for every finite `S ⊆ N` some `g^D`, `D ≥ 1`,
centralizes `S`.

**Theorem E2 (H is Schottky in the third tree).** Every nontrivial element
of `H` acts on `T_a` as a hyperbolic automorphism. Hence:
1. `H` acts freely (and without inversions) on `T_a`, so `H` is a
   **finitely generated free group**, `pr_a` is injective on `H`, and
   `pr_a(H)` is discrete and acts cocompactly on its minimal subtree.
2. `N` is an infinitely generated, non-abelian free normal subgroup of
   `H` for **every** infinite `P` (Theorem D needed a non-cyclic finite
   subgroup of `L`).
3. No element of `H` mapping to `P ∖ L` fixes a point of `T_a`.

**Theorem E3 (two killing criteria).**
1. **Discrete cut-out projection.** If `ρ(H)`, `pr_b(H)` or `pr_c(H)` is
   discrete (e.g. `Λ` reducible as `Λ_a × Λ_{bc}`, `Λ_{ab} × Λ_c` or
   `Λ_{ac} × Λ_b`), there is no such cut-out.
2. **Core criterion.** Suppose `pr_a` is injective on `Λ`. Let
   `Σ_H = ⋂_{h ∈ H} hΣh^{-1}`. If `pr_a(Σ_H)` is a uniform lattice of
   `G_a` (e.g. `Λ` cocompact and `Σ_H` of finite index in `Σ`; or
   `Ĥ = cl ρ(H)` normalizes some compact open `U ≤ K` and `Λ` is
   cocompact), there is no such cut-out. So a surviving witness needs
   `[Σ : Σ_H] = ∞`, i.e. `K` contains no open subgroup normalized by `Ĥ`.

**What survives (the sharpened target).** A realization of `Z/2 ≀ Z` in a
torsion-free cocompact irreducible three-tree lattice is exactly a
Schottky pair: `H = ⟨a_1, …, a_k⟩` free acting freely on `T_a`, with both
`pr_b(H)`, `pr_c(H)` non-discrete and non-linear (Theorem C), whose
`(b, c)`-closure is compact-by-`P` with the compact part fixing
`Y_b × Y_c` pointwise and normalizing no open subgroup of `K`. The
abstract model `F_2 = ⟨a, t⟩ ↠ Z/2 ≀ Z` has exactly this shape, so E does
not kill by itself.

**Calibration.**
- *Abstract hosts are realizable.* Without the lattice condition the shape
  is attained: `F_2 ↪ P × M` via `(π, ψ)` with `ψ` an embedding of `F_2`
  into a profinite `M`, `P × M` acting on `DL(2,2)` with `M` acting on
  hairs; `K` a vertex stabilizer gives `H ∩ ρ^{-1}(K) = ker π`. Here `Σ`
  is not finitely generated, so the lattice (type `F`) hypothesis is what
  E3.2 and the open problem are about.
- *Torsion calibrates E1.* The discrete `DL(2,2)` action of `Z/2 ≀ Z`
  has elliptic lamps; E2 does not apply since there `N = 1`.

Proof: route `lamplighter-cut-outs-act-freely-on-the-third-tree-proof`.

## Attempts

- 2026-09-19 (w19-117): E1–E3 proved. Proposed-established. Open: in a
  non-arithmetic irreducible torsion-free cocompact three-tree lattice
  (Rattaggi, Kimberley–Robertson, Burger–Mozes type), find a Schottky
  pair as above, or show `Λ ∩ (G_a × Fix(ℓ_b × ℓ_c)) = 1` for every flat
  of an element hyperbolic in `b` and `c`. For cube-complex lattices
  acting simply transitively on vertices this is a finite-state
  (Mealy-automaton) question on `a`-words, and is searchable.
