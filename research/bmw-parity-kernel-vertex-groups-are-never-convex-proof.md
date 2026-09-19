---
rg: 2
id: bmw-parity-kernel-vertex-groups-are-never-convex-proof
kind: route
title: Proof via the invariant order on the cosets of a convex subgroup, finite orbits of vertex stabilizers on spheres, and Burger–Mozes discreteness
target: bmw-parity-kernel-vertex-groups-are-never-convex
requires: []
---

# Proof

## 1. Cosets of a convex subgroup

Let `(G, <)` be left-ordered and `H ≤ G` convex: if `h_1 < x < h_2` with `h_i ∈ H`, then `x ∈ H`.

**Order on the cosets.** For distinct cosets set `xH ≺ yH` iff `x < y`. This is well defined, which is
standard. Let `x < y` with `xH ≠ yH`.
- `xh < y` for every `h ∈ H`. Otherwise `x < y < xh`, and left multiplication by `x^{-1}` gives
  `1 < x^{-1}y < h`, so `x^{-1}y ∈ H` by convexity.
- `x < yh'` for every `h' ∈ H`. Otherwise `yh' < x < y` gives `h' < y^{-1}x < 1`.
- Applying the second point to `xh < y` gives `xh < yh'` for all `h, h' ∈ H`.

So `≺` does not depend on the representatives. It is a total order on `G/H`, and left multiplication
preserves it because `<` is left-invariant.

**Proof of the Lemma.** An order-preserving bijection of a totally ordered set that has a finite orbit
fixes that orbit pointwise. Indeed, if `σ(p) ≻ p`, then `p ≺ σ(p) ≺ σ²(p) ≺ ⋯` is strictly increasing,
so the orbit is infinite. The `H`-orbit of `gH` in `G/H` has `[H : H ∩ gHg^{-1}]` points, so it is
finite. So every `h ∈ H` fixes `gH`, that is `g^{-1}hg ∈ H`, and `g^{-1}Hg ⊆ H`. Applying the same to
`g^{-1}` gives `gHg^{-1} ⊆ H`, hence `H ⊆ g^{-1}Hg`. Together, `g^{-1}Hg = H`. ∎

## 2. The coset space `Γ^+/B^+`

Every `g ∈ Γ^+` is uniquely `g = a b` with `a ∈ A`, `b ∈ B` reduced. The squares preserve the number
of `h`-letters and the number of `v`-letters, so the parity map `Γ → (ℤ/2)²` is a homomorphism. Hence
`|a|` and `|b|` are even, so `a ∈ A^+` and `b ∈ B^+`. The map `aB^+ ↦ a` is therefore a bijection
`Γ^+/B^+ → A^+`, and `A^+` is the set of vertices of `T_A` at even distance from the root.

Under this bijection, left multiplication by `β ∈ B^+` is the automaton action. If `β a = a' b'`, then
`β · aB^+ = a' b' B^+ = a' B^+`. The automaton action of `B` on reduced `A`-words preserves length,
since it is the action of the stabilizer `B` of the base vertex of the tree `Γ/B = T_A` by tree
automorphisms. So each `B^+`-orbit on `A^+` lies in one sphere of `T_A`, and it is finite.

## 3. Proof of the Theorem

Let `B^+` be convex in `<`. By §1 applied to `G = Γ^+` and `H = B^+`, `B^+` fixes every point of every
finite `B^+`-orbit in `Γ^+/B^+`. By §2 that is every point. So each `β ∈ B^+` fixes every vertex of
`T_A` at even distance from the root.

`T_A` is `m`-regular with `m ≥ 2`. An odd vertex `u` is the midpoint of the geodesic between two of its
neighbours `w_1 ≠ w_2`, which are even vertices. A tree automorphism fixing `w_1` and `w_2` fixes that
geodesic, and so fixes `u`. Hence `B^+` acts trivially on `T_A`. Since `[B : B^+] = 2`, the image of
`B` in `Aut(T_A)` has order at most 2. The statement for `A^+` is the same with the letters exchanged.

For a conjugate, let `g ∈ Γ`. `Γ^+` is normal, being a kernel, so `x ↦ g^{-1}xg` is an automorphism of
`Γ^+` that maps `gB^+g^{-1} = Γ^+ ∩ gBg^{-1}` onto `B^+`. Transporting `<` along it turns convexity of
`gB^+g^{-1}` into convexity of `B^+`. `Γ^+ ∩ gBg^{-1}` is the `Γ^+`-stabilizer of the vertex `gB` of
`T_A = Γ/B`. ∎

(The Lemma gives the same conclusion as §2–§3: `B^+` is commensurated by `Γ^+`, since
`B^+ ∩ aB^+a^{-1}` is the stabilizer of a vertex in a finite orbit. So a convex `B^+` would be normal,
and a normal vertex stabilizer fixes the whole orbit `Γ^+ · B`, which is the even vertices.)

## 4. Proof of the Corollary

The image of `B` in `Aut(T_A)` is the stabilizer of the base vertex in `pr_A(Γ) ≤ Aut(T_A)`. Indeed
`pr_A(g)` fixes the vertex `B` iff `gB = B` iff `g ∈ B`. If that image is finite, then `pr_A(Γ)` is
discrete. For a cocompact lattice `Γ < Aut(T_A) × Aut(T_B)`, discreteness of one projection implies
that `Γ` is reducible. This is Burger–Mozes, *Lattices in product of trees*, Publ. IHÉS 92 (2000),
Prop. 1.2.

Sketch. Let `Λ = ker(pr_A|Γ)`. Vertex stabilizers of `pr_A(Γ)` are finite, so `Λ` has finite index in
every `Γ`-stabilizer of a vertex of `T_A`. Such a stabilizer acts cocompactly on `T_B`, so `Λ` is a
uniform lattice in `Aut(T_B)`. Its normalizer `pr_B(Γ)` is then discrete, because a uniform tree
lattice has trivial centralizer and so a discrete normalizer. Hence `Γ` is virtually
`ker(pr_A) × ker(pr_B)`, a product of free groups.

So for irreducible `Γ` both images are infinite, and by the Theorem neither vertex group, nor any of
its conjugates in `Γ^+`, is convex.

**Lexicographic orders.** Suppose a left order `<` on `Γ^+` is lexicographic with respect to
`B^+ ≤ Γ^+`. That means `x < y` whenever `xB^+ ≺ yB^+` for some `Γ^+`-invariant total order `≺` on
`Γ^+/B^+`, and `B^+` is ordered inside. Then `B^+` is convex: if `β_1 < x < β_2` with `β_i ∈ B^+` and
`xB^+ ≠ B^+`, then `xB^+ ≺ B^+` and `B^+ ≺ xB^+` would both have to hold. So lexicographic orders are
excluded.

Conversely, suppose `B^+` acts trivially on `T_A`. Then `B^+ = ker(pr_A) ∩ Γ^+` is normal. The group
`Γ^+/B^+ ≅ pr_A(Γ^+)` acts on `T_A` with trivial vertex stabilizers and without inversions, since
parity is preserved, so it is free. Lexicographic extension of a left order of `B^+` by one of this
free quotient then works. So the dichotomy is sharp at the level of this
construction. ∎

## 5. Proof of Theorem 2 (normal closures)

Let `C` be convex in `<` with `[B^+ : B^+ ∩ C] < ∞`.

**Step 1: `B^+ ⊆ C`.** The `B^+`-orbit of the coset `C` in `Γ^+/C` has `[B^+ : B^+ ∩ C]` points, so it
is finite. By §1 it is fixed pointwise, so `B^+ C = C`.

**Step 2: `N_B ⊆ C`.** Let `g ∈ Γ^+`. The `B^+`-stabilizer of `gC` is `B^+ ∩ gCg^{-1}`, which contains
`B^+ ∩ gB^+g^{-1}` by Step 1. That group has finite index in `B^+`. It has index at most 2 in
`B^+ ∩ gBg^{-1}`, the `B^+`-stabilizer of the vertex `gB` of `T_A`, and the `B^+`-orbit of that vertex
lies in one sphere of `T_A`. So the orbit of `gC` is finite, and by §1 it is fixed. Hence
`g^{-1}B^+g ⊆ C` for every `g ∈ Γ^+`, that is `N_B ⊆ C`.

**Step 3: `Γ^+/N_B ≅ A^+/M`.** Define `φ : Γ^+ → A^+/M` by `φ(ab) = aM` for the normal form `g = ab`
(`a ∈ A^+`, `b ∈ B^+` by §2). It is a homomorphism. Write `b_1 a_2 = (b_1·a_2) b''`. Then
`a_1b_1a_2b_2 = a_1(b_1·a_2) · b''b_2`, and `a_2^{-1}(b_1·a_2) ∈ M`. So
`φ(g_1g_2) = a_1(b_1·a_2)M = a_1a_2M`, using that `M` is normal in `A^+`. Its kernel contains `B^+`, and
it is normal, so it contains `N_B`. Conversely `a^{-1}(β·a) = a^{-1}βaβ'^{-1} ∈ N_B`, so `M ⊆ N_B`. If
`ab ∈ ker φ`, then `a ∈ M ⊆ N_B` and `b ∈ N_B`. So `ker φ = N_B`, and `φ` is onto.

**Step 4: generators of `M`.** Let `a = a_1a_2` be reduced with `|a_1| = 2` and `|a_2|` even. Write
`βa_1 = (β·a_1)β'`, with `β' ∈ B^+` by parity. Then `β·a = (β·a_1)(β'·a_2)` and
`a^{-1}(β·a) = a_2^{-1}[a_1^{-1}(β·a_1)]a_2 · a_2^{-1}(β'·a_2)`. By induction on `|a|`, the elements
with `|a| = 2` normally generate `M`. For `β = β_1β_2`,
`a^{-1}(β·a) = [a^{-1}(β_2·a)] · [a'^{-1}(β_1·a')]` with `a' = β_2·a`, which also has length 2. So `β` may
run over a generating set of `B^+`. The generators are the relations `w = w'` for `w, w'` in one
`B^+`-orbit of `S_2(T_A)`.

**Step 5: the transitive case.** Suppose `B^+` is transitive on `S_2(T_A)` and `m ≥ 3`. Then all
reduced words of length 2 have the same image `q ∈ A^+/M`. Choose letters `x`, `y ≠ x^{-1}` and
`z ∉ {y, x^{-1}}`, which is possible because `m ≥ 3`. Then `(xy)(y^{-1}z) = xz` is reduced of length 2.
So `q·q = q` and `q = 1`. The words of length 2 generate `A^+`, so `A^+/M = 1`.

**Conclusion.** If `Q_B` is finite and `C ⊇ N_B`, then `[Γ^+ : C] < ∞`. The `Γ^+`-orbit `Γ^+/C` is
finite, so by §1 it is fixed and `C = Γ^+`. For a conjugate `gB^+g^{-1}` with `g ∈ Γ`, transport the
order along conjugation, as in §3. The quotient by its normal closure is again isomorphic to `Q_B`. ∎

**Computation.** `experiments/bmw-beyond-census-sampling-2026-09-19/qsphere.py` computes the
`B^+`-orbits on `S_2(T_A)` and the `A^+`-orbits on `S_2(T_B)` for every census class that is not
certified reducible. In the transitive case with degree at least 3 it reports `Q = 1` by Step 5.
Otherwise it runs GAP: the Reidemeister–Schreier presentation of the even subgroup, plus the orbit
relations, then abelian invariants and coset enumeration capped at 200000 cosets. The output is
`qsphere.jsonl`.

## 6. Scope

- **What this does not do.** It does not refute left-orderability of any `Γ^+`. It restricts every
  potential left order, uniformly in the degrees: its convex subgroups avoid all vertex stabilizers
  and all commensurated non-normal subgroups.
- **Why the census certificates are still needed.** An `h`-length or `v`-length is not an order
  invariant. The certificates of `bmw-census-solver-free-parity-kernel-certificates` refute the
  remaining, non-lexicographic orders case by case.

## 7. The beyond-census samples

Each certificate is checked by code that trusts no solver answer.
- **Cone trees.** They are checked independently (`check_tree`).
- **Cone lemmas.** The CNF is re-derived clause by clause from the normal form (`semcheck`). Every lemma is
  RUP-checked by `rup.cpp`, and the trimmed core is checked again.
- **50_40 seed 107.** The four identities `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}` are checked by `kverify.py`, from
  the squares alone. Lemma 1 of `bmw-40-40-193-281-332-klein-chain-proof` (applied with `a = x_{i+1}`, `b = x_i`) then gives
  `|x_0| < |x_1| < |x_2| < |x_3| < |x_0|`, which is impossible.

**Universality.** Suppose `Γ^+` is not left-orderable. By compactness (a group is left-orderable iff each
finite subset admits a consistent partial positive cone), there is a radius `R` at which the ball instance
is unsatisfiable. Branching on "`x` or `x^{-1}`" for the variables of that instance gives a finite cone
tree. So cone trees, and likewise RUP cone lemmas, are complete. A Klein-type chain needs an element that
is inverted by conjugation, so it is not complete.
