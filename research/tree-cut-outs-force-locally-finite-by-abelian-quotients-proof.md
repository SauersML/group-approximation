---
rg: 2
id: tree-cut-outs-force-locally-finite-by-abelian-quotients-proof
kind: route
title: "Proof: the closure of rho(H) is compact-open-normal-by-P, so amenable; amenable closed subgroups of Aut(T) are bounded, pair-of-ends or end-fixing, each with a Busemann/translation character to Z whose kernel is locally elliptic; the kernel's image in the discrete P is locally finite; for A wr Z the factorwise parabolic lemma forces opposite orientations, and normality of M under the shift makes M fix the whole axes and their orbit hulls"
target: tree-cut-outs-force-locally-finite-by-abelian-quotients
requires:
  - ascending-completions-give-only-virtually-cyclic-quotients
  - rank-one-cut-outs-kill-amenable-non-abelian-quotients
---

Verification tier: proposed-established. Ingredients: the compact-open-normal
step and parabolic lemma of
`ascending-completions-give-only-virtually-cyclic-quotients` (item 1), the
classification of closed amenable subgroups of `Aut(T)` for locally finite
`T` (Nebbia 1988; Adams–Ballmann 1998, Thm. for proper CAT(0) spaces), and
elementary tree geometry.

## Step 0: set-up

`P ≅ H/(H ∩ Σ)` and `H ∩ Σ = H ∩ ρ^{-1}(K)`. Let `Ĥ` be the closure of
`ρ(H)` in `G` and `M = Ĥ ∩ K`. Since `ρ(H) ∩ K = ρ(H ∩ Σ)` is normal in
`ρ(H)` and dense in the open set `M` of `Ĥ`, `M` is normalized by `ρ(H)`
and hence by `Ĥ`. `M` is compact open in `Ĥ`, and
`ρ(H)/(ρ(H) ∩ K) -> Ĥ/M` is an isomorphism (surjective by density plus
openness of `M`, injective by definition). The kernel of `H -> ρ(H)` lies
in `ρ^{-1}(1) ⊆ ρ^{-1}(K)`, so `P ≅ Ĥ/M` as abstract groups, with `Ĥ/M`
discrete.

If `P` is amenable then `Ĥ` is amenable (compact-by-amenable), and so is
each projection closure `Ĥ_j = cl pr_j(Ĥ) ≤ Aut(T_j)`.

## Step 1: amenable closed subgroups of Aut(T)

For `T` locally finite, a closed amenable `A ≤ Aut(T)` satisfies one of:

- (i) **bounded**: `A` fixes a vertex or stabilizes an edge; then `A` is
  compact.
- (ii) **pair of ends**: `A` stabilizes a set `{ξ, η}` of two ends and
  fixes no vertex. The subgroup `A^+` fixing both ends has index `≤ 2`,
  and the translation length along the axis `(ξ, η)` is a continuous
  homomorphism `A^+ -> Z` whose kernel fixes the axis pointwise, so is
  compact.
- (iii) **one end**: `A` fixes a unique end `ξ`. The Busemann character
  `β_ξ : A -> Z`, `β_ξ(g) = b_ξ(x) - b_ξ(gx)` (independent of `x`), is a
  continuous homomorphism. Its kernel `A_0` consists of elliptic elements:
  an element fixing `ξ` is hyperbolic iff its axis ends at `ξ`, and then
  `β ≠ 0`.

The trichotomy is Nebbia's theorem (and the case `X = T` of
Adams–Ballmann: an amenable group of isometries of a proper CAT(0) space
fixes a point at infinity or stabilizes a flat; for a tree, a flat is a
point or a line).

**Local ellipticity in (iii).** Every finitely generated subgroup of `A_0`
has compact closure. Indeed each `g ∈ A_0` is elliptic and fixes `ξ`, so it
fixes a vertex `x_g` and hence the whole ray `[x_g, ξ)`. Finitely many rays
to the same end have a common subray, so a finite set in `A_0` fixes a
common vertex, and vertex stabilizers are compact open.

In all cases put `A^♮ = A` in (i) and (iii) and `A^♮ = A^+` in (ii), and
`χ_A : A^♮ -> Z` the zero map in (i), the translation character in (ii),
`β_ξ` in (iii). Then `[A : A^♮] ≤ 2`, `χ_A` is continuous, and every
finitely generated subgroup of `ker χ_A` has compact closure.

## Step 2: proof of Theorem A

Let `Ĥ' = {g ∈ Ĥ : pr_j(g) ∈ Ĥ_j^♮ for all j}`, a closed subgroup of index
`≤ 2^s`, and `χ = (χ_{Ĥ_1} ∘ pr_1, ..., χ_{Ĥ_s} ∘ pr_s) : Ĥ' -> Z^s`,
continuous. Let `Ĥ'_0 = ker χ`.

- `χ(M ∩ Ĥ') = 0`, because it is a compact subgroup of `Z^s`. So `χ`
  factors through `P' := Ĥ'M/M ≅ Ĥ'/(M ∩ Ĥ')`, a subgroup of `P` of index
  `≤ 2^s`. Call the induced map `χ̄ : P' -> Z^s`.
- `ker χ̄` is the image of `Ĥ'_0 (M ∩ Ĥ')`, which is the image of `Ĥ'_0`
  since `M ∩ Ĥ' ⊆ Ĥ'_0`.
- Let `S ⊆ ker χ̄` be finite and lift it to a finite `S̃ ⊆ Ĥ'_0`. For each
  `j`, `pr_j⟨S̃⟩ ≤ ker χ_{Ĥ_j}` is finitely generated, so has compact
  closure by Step 1. Hence `⟨S̃⟩` has compact closure `C` in `G`, and
  `C ⊆ Ĥ` since `Ĥ` is closed. The image of `C` in the discrete group
  `Ĥ/M` is compact, hence finite. So `⟨S⟩` is finite.

Thus `ker χ̄` is locally finite and `P'/ker χ̄ ↪ Z^s`. ∎

**Corollary 1.** If `P` is torsion-free, `ker χ̄` is torsion-free and
locally finite, hence trivial; so `P' ↪ Z^s` and `P` is virtually `Z^k`.
`BS(1,n)` (`n ≥ 2`), `Z ≀ Z` and the Heisenberg group are not virtually
abelian.

**Corollary 2.** If `P` is a torsion group, `χ̄(P')` is a torsion subgroup
of `Z^s`, so `P' = ker χ̄` is locally finite. If `P` is finitely generated,
so is `P'` (finite index), hence `P'` and `P` are finite. Grigorchuk's
group is finitely generated, infinite, amenable and torsion.

## Step 3: proof of Theorem B

Let `P = L ⋊ ⟨t⟩` as in the statement, with `L ≠ 1`. Then `L` is
infinite: if `L` were finite, conjugation by `t` would have finite order
`d` on `L`, so `L = C_L(t^d) = 1`. `P` is amenable (locally finite-by-`Z`),
so Theorem A applies; take `P'`, `χ`, `Ĥ'` from Step 2.

**Choice of `τ` and a lamp.** Choose `m ≥ 1` with `t^m ∈ P'`. `Ĥ'` is
closed of finite index, hence open, so `Ĥ' ∩ τ'M` is a nonempty open set
for any lift `τ'` of `t^m` in `Ĥ'`, and it meets the dense `ρ(H)`. Pick
`τ₀ ∈ H` with `τ = ρ(τ₀)` in it. `L ∩ P'` has finite index in the infinite
`L`, so contains `ℓ ≠ 1`; lift it to `x ∈ Ĥ'`. `χ̄(ℓ)` is torsion in
`Z^s`, so `χ(x) = 0` and `x ∈ Ĥ'_0`.

**`χ(Ĥ')` is cyclic.** `χ̄` kills the locally finite `L ∩ P'`, so it
factors through `P'/(P' ∩ L)`, a subgroup of `⟨t⟩`. Hence `χ̄(P')` is
cyclic, generated by `χ̄(g)` for some `g` with image `t^{m'}`, and
`χ(τ) = (m/m')·χ̄(g)`. So `χ_j(τ) = 0` implies `χ_j = 0` on `Ĥ'`.

**B1.** The parabolic lemma (item 1 of
`ascending-completions-give-only-virtually-cyclic-quotients`) says that if
`{τ^n x τ^{-n} : n ≥ 0}` is relatively compact then `ℓ ∈ C_P(t^{md})` for
some `d ≥ 1`. But `C_L(t^{md}) = 1`. Applying the lemma to `τ^{-1}` as
well, **neither** the forward nor the backward conjugates of `x` are
relatively compact in `G`. A subset of `G` is relatively compact iff each
projection is. Examine each factor `j`, writing `A = Ĥ_j`:

- (i) `A` compact: both orbits bounded.
- (ii) `pr_j x ∈ ker χ_A` fixes the axis pointwise; `pr_j τ` preserves the
  axis; so every `τ^n x τ^{-n}` lies in the compact axis fixator.
- (iii) with `β_j(τ) = 0`: `pr_j⟨τ, x⟩ ≤ ker β_j` is finitely generated,
  so has compact closure (Step 1).
- (iii) with `β_j(τ) > 0`: `pr_j τ` is hyperbolic with axis `ℓ_j` ending at
  `ξ_j` and translates towards `ξ_j`. `pr_j x` fixes a ray `[y, ξ_j)`, and
  we may take `y ∈ ℓ_j`. Then `τ^{-n} x τ^n` fixes
  `τ^{-n}[y, ξ_j) = [τ^{-n}y, ξ_j) ∋ y` for `n ≥ 0`, because `τ^{-n}y`
  lies on `ℓ_j` on the far side of `y` from `ξ_j`. So the backward
  conjugates lie in the compact `Stab(y)`.
- (iii) with `β_j(τ) < 0`: symmetrically, the forward conjugates are
  bounded.

If no factor had `β_j(τ) > 0`, the forward conjugates would be bounded in
every factor, a contradiction. If none had `β_j(τ) < 0`, the backward ones
would be. So there are one-end factors `j ≠ k` with `β_j(τ) > 0 > β_k(τ)`. ∎

**B2.** Let `j ∈ J`. `pr_j M` is compact and normalized by `pr_j τ`.
- Type (iii): `pr_j M` fixes a vertex and `ξ_j`, hence a ray `[y, ξ_j)`
  with `y ∈ ℓ_j`. `Fix(pr_j M)` is `τ`-invariant, so contains
  `τ^k[y, ξ_j)` for all `k ∈ Z`, whose union is `ℓ_j` (as `β_j(τ) ≠ 0`).
- Type (ii): `pr_j M` preserves the axis `ℓ_j` and acts on it through a
  finite subgroup of `Isom(ℓ_j) ≅ D_∞`, i.e. `1` or `{1, r}` with `r` a
  reflection. It is normalized by the nontrivial translation `pr_j τ`, and
  `τ r τ^{-1}` is a reflection about a different point, so the image is
  `1`: `pr_j M` fixes `ℓ_j` pointwise.

Since `M ⊴ Ĥ`, `g·Fix(pr_j M) = Fix(pr_j(gMg^{-1})) = Fix(pr_j M)` for
`g ∈ Ĥ`, so `Fix(pr_j M) ⊇ Ĥ·ℓ_j`. Fixed-point sets in trees are
subtrees, so `Fix(pr_j M) ⊇ Y_j`.

Let `Ker` be the kernel of `Ĥ` on `∏_{j∈J} Y_j`. For `g ∈ Ker ∩ Ĥ'` and
`j ∈ J`, `pr_j g` fixes `ℓ_j`, so `χ_j(g) = 0`; for `j ∉ J`, `χ_j = 0` on
`Ĥ'` by the cyclicity above. So `Ker ∩ Ĥ' ⊆ Ĥ'_0`, whose image in `P` is
the locally finite `ker χ̄`. As `[Ker : Ker ∩ Ĥ'] < ∞`, `Ker/M` is
locally finite.

If each factor outside `J` has compact image, `Ker` is contained in
(vertex stabilizers) × (compact), so is compact; then `Ker/M` is a finite
normal subgroup of `P`, hence trivial (a finite normal subgroup lies in
`L`, as `P/L ≅ Z`, and is normalized by `t`, so it is centralized by some
`t^d`). The `Ĥ`-stabilizer of a vertex of `∏_J Y_j` is compact and open,
so its image in `P` is finite: the action of `P = Ĥ/M` is faithful and
proper. ∎

**B3.** Suppose `Λ` torsion-free and `ρ|_H` injective. If `M` were finite,
`ρ(H) ∩ M` would be a finite subgroup of `ρ(H) ≅ H`, hence trivial, and
dense in the open `M`; so `M = 1`, `H ∩ Σ = H ∩ ρ^{-1}(M) = 1`, and
`P ≅ H` would be torsion-free, contradicting `1 ≠ L`. So `M` is infinite,
`H ∩ Σ ≠ 1` (else `P ≅ H` again), and `ρ(H ∩ Σ) ⊆ M` fixes
`∏_J Y_j ⊇ ∏_J ℓ_j`, the flat of `τ = ρ(τ₀)`. ∎

## Step 4: Corollary B′ and the three-tree form

B′ is B3 read contrapositively, since `τ₀` is hyperbolic in the two
factors of B1.

Let `Λ ≤ G_a × G_b × G_c` be a torsion-free lattice with `ρ = pr_{bc}`
injective, cut out by `K ≤ G_b × G_c`. Then `J = {b, c}` by B1, and
`Λ_F = Λ ∩ (G_a × Fix(ℓ_b) × Fix(ℓ_c))` contains `H ∩ Σ ≠ 1`.
- `Λ_F` lies in `Λ ∩ (G_a × C)` with `C` compact, so its projection to
  `G_a` is discrete, and injective because `Λ ∩ (1 × C)` is finite, hence
  trivial.
- A torsion-free discrete subgroup of `Aut(T_a)` has trivial vertex
  stabilizers (they are finite), and no inversions (the square of an
  inversion fixes an edge). So `Λ_F` acts freely on `T_a` and is free.
- `τ₀` preserves `ℓ_b × ℓ_c`, so it normalizes `Λ_F`.

**Literal DL(2,2).** If `s = 2` and `Y_b = T_b`, `Y_c = T_c` (as for the
`DL(2,2)` action of `Z/2 ≀ Z`, whose orbit of the shift axes spans both
trees), then `M` acts trivially on `T_b × T_c`, so `M = 1`, contradicting
B3. A nondiscrete witness therefore needs proper hulls `Y_j`. ∎

## What is left

The `Aut(T)` case is now the question whether a torsion-free irreducible
lattice in three trees can have `1 ≠ H ∩ Σ ⊆ Λ_F` for a finitely
generated `H` with `H/(H ∩ Σ) ≅ Z/2 ≀ Z`. Two ways to finish:
- prove `Λ_F = 1` for every bi-hyperbolic `τ₀` (plausible when the local
  actions are 2-transitive, by a Burger–Mozes-type normal subgroup
  argument on the ray fixators); this kills the `Aut(T)` case;
- or find a lattice (e.g. from a non-residually-finite Wise/Burger–Mozes
  square complex crossed with a third tree) with a nontrivial flat
  fixator, and build `H` inside `Λ_F ⋊ ⟨τ₀⟩` together with lamp elements
  fixing `ξ_b`, `ξ_c`.
