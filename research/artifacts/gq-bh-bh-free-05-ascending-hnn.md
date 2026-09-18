# Ascending HNN extensions of free groups satisfy Boone–Higman (bh-free-05, 2026-09-18)

Lane proof, not independently reviewed. No priority claimed (bounded search below).

## 1. Source read

K.-U. Bux, C. Llosa Isenrich, X. Wu, *On the Boone–Higman Conjecture for groups acting on
locally finite trees*, arXiv:2408.05673v2, TeX e-print fetched via MSI on 2026-09-18
(`main.tex`, SHA-256 `f3509384840202384392b73ea6f3e8f6bec3ca8df29fd16046231affebea2ac0`,
kept at `$GQ/src/bh-free-05/bliw-2408.05673v2.tex`). Displayed theorem numbers are not
pinned; the TeX labels are.

- **Definition of BS_G (§11, TeX line 927):** "Given a group $G$ we denote by $\BSol_G$ the
  class of groups consisting of all (finite) graphs of groups with the property that all edge
  and vertex groups are abstractly commensurable with $G$ and all edge group inclusions in
  vertex groups have finite index."
- **`thm:free-groups` (§12.5, lines 1016–1018):** "Let $G=\mathbb{F}_k$ for $k\geq 2$ be
  $k$-generated non-abelian free. Then every group in $\BSol_{\mathbb{F}_k}$ embeds in a simple
  group of type $F_{\infty}$. In particular, non-abelian finitely generated free by cyclic groups
  satisfy the Boone--Higman Conjecture."
  Its proof uses `thm:main-BS` (= Theorem C / 11.1) with a Burger–Mozes amalgam
  $\mathbb{F}_n *_H \mathbb{F}_n$ as the faithful member of $\BSol_{\mathbb{F}_2}$.
- **`rem:burger-mozes` (lines 1039–1041):** "Our proof of Theorem \ref{thm:free-groups} shows
  that for every group in $\BSol_{\mathbb{F}_k}$ the permutational Boone--Higman Conjecture
  holds, that is, every such group embeds in a finitely presented group that admits an action
  of type (A) on a countable set in the sense of Zaremsky ..."

The paper applies this only to free-by-cyclic groups (surjective φ). For non-surjective φ the
Bass–Serre tree of F*_φ is not locally finite, which is exactly why
`power-map-free-mapping-tori-satisfy-permutational-boone-higman` says BLIW "do not apply as
stated" and leaves general injective endomorphisms open (its test case φ(x)=xy, φ(y)=yx).

## 2. The theorem

Let F be a finitely generated free group, φ: F → F an injective endomorphism, and
Γ = F*_φ = ⟨F, t | t g t⁻¹ = φ(g), g ∈ F⟩. Then Γ embeds in a group H ∈ BS_{F_2}.
Consequently (thm:free-groups, rem:burger-mozes) Γ embeds in a simple group of type F_∞, and
Γ embeds in a finitely presented group with an action of type (A). So Γ and all its
finitely generated subgroups satisfy BH and permutational BH.

(Rank 0 is trivial. Rank n ≥ 1 is handled uniformly below; n = 1 recovers BS(1,m).)

## 3. Proof

Write F = F(a_1,…,a_n), n ≥ 1, K = φ(F) (free of rank n, φ: F → K an isomorphism).
Put Y = F * ⟨b⟩, free of rank n+1 ≥ 2.

**Step 1 (M. Hall, self-contained).** There is a finite-index C_2 ≤ Y with K a free factor
of C_2. Proof by Stallings folding: let Γ_K be the finite folded Y-labelled graph with
basepoint v_0 whose π_1 is K (fold a bouquet of the generators of K). For each letter
x ∈ {a_1,…,a_n,b}, the x-edges of Γ_K define a partial injection of the finite vertex set V;
extend it to a permutation of V by adding x-edges (the missing domain and range points have
the same count). The resulting graph Γ' has vertex set V, is connected, and every vertex has
exactly one incoming and one outgoing edge of each label, so it is a |V|-sheeted cover of
the rose; hence C_2 := π_1(Γ', v_0) has index d := |V| in Y. A maximal tree T of Γ_K is a
maximal tree of Γ' (same vertices). The free basis of C_2 given by the edges of Γ' outside T
contains the free basis of K given by the edges of Γ_K outside T. So C_2 = K * L.

**Step 2.** Let π: Y → Z/d, a_i ↦ 0, b ↦ 1, and C_1 = ker π, of index d. Its covering graph
has vertices Z/d, an a_i-loop at every vertex, and b-edges k → k+1. With the maximal tree
formed by the b-edges 0 → 1 → … → d−1, the a_i-loops at 0 contribute the basis elements a_i.
So C_1 = F * R.

**Step 3.** By Schreier, rank C_1 = rank C_2 = d·n + 1. By additivity of rank under free
products of free groups, rank R = rank C_1 − n = rank C_2 − n = rank L. Choose an isomorphism
α: R → L and put Φ = φ * α: C_1 = F * R → K * L = C_2, an isomorphism with Φ|_F = φ.

**Step 4.** H := Y*_Φ = ⟨Y, s | s c s⁻¹ = Φ(c), c ∈ C_1⟩ is a one-vertex, one-edge graph of
groups. The vertex group Y (rank n+1) and edge group C_1 (rank dn+1) are non-abelian free of
finite rank, hence commensurable with F_2, and both edge inclusions (C_1 ≤ Y and
Φ(C_1) = C_2 ≤ Y) have index d. So H ∈ BS_{F_2}.

**Step 5 (injectivity).** Define θ: Γ → H by θ|_F = (F ≤ Y), θ(t) = s. It is well defined
because s g s⁻¹ = Φ(g) = φ(g) for g ∈ F.
- Let B = ⋃_{k≥0} t^{-k} F t^{k} ⊆ Γ. It is an increasing union, since
  F = t⁻¹ φ(F) t ⊆ t⁻¹ F t. It is normal, since t B t⁻¹ = B, and Γ/B ≅ Z via t ↦ 1, F ↦ 0.
- θ is injective on F, hence on each conjugate t^{-k}Ft^{k}, hence on the increasing union B.
- Let ε: H → Z be s ↦ 1, Y ↦ 0 (it respects the relations, since both sides lie in Y). Then
  ε∘θ: Γ → Z is t ↦ 1, F ↦ 0, whose kernel is B. So ker θ ⊆ B, and ker θ = ker θ ∩ B = 1.
∎

Note: the HNN subgroup criterion (F ∩ C_2 = φ(F)) fails here, since F ∩ C_2 has finite index
in F, as recorded in (L3) of `finite-index-edge-hnn-embeds-in-fp-simple-group`. Step 5 is the
different argument that (L3) asks for, available because the extension is ascending.

## 4. Examples and consequences

- **Sapir's Thue–Morse test case** ⟨x, y, t | t x t⁻¹ = xy, t y t⁻¹ = yx⟩ (φ(x)=xy,
  φ(y)=yx, injective since φ(F_2) = ⟨xy, yx⟩ has rank 2) satisfies BH and PBH. It was the
  open test case of `power-map-free-mapping-tori-satisfy-permutational-boone-higman`.
- **Druţu–Sapir group** ⟨a, t | a^{t²} = a²⟩ (arXiv math/0405470: non-linear, residually
  finite, one-relator). This is a second proof; main already has
  `drutu-sapir-group-satisfies-boone-higman` via power maps.
- **Free-by-cyclic groups** (φ surjective) are the BLIW case.
- **One-relator groups.** Every one-relator group that is an ascending HNN extension of a
  finitely generated free group is covered. This is not a claim about all one-relator groups.
  The Magnus–Moldavanskii criterion (an extremal-index letter occurring once) is standard, but
  it was not re-derived here.
- **Subgroups.** Every finitely generated subgroup of such a Γ is covered, since BH passes to
  subgroups.

## 5. Scope and checks

- **Imported:** only BLIW `thm:free-groups` and `rem:burger-mozes` (with their Burger–Mozes
  input), read at source.
- **Proved here:** Hall's theorem (Step 1) and the rest.
- **Priority:** the arXiv API query `all:"Boone Higman"` (16 entries, 2013–2026, including
  BLIW, BFFHZ, FWZ, FFKLZ, Zaremsky, BHM, and 2609.01868) found no abstract mentioning
  ascending HNN extensions or free-group endomorphisms. Main's own nodes list the general case
  as open. This is a bounded search: no MathSciNet, no Google Scholar.
- **Not claimed:** HNN extensions of free groups with both associated subgroups of infinite
  index, where Step 5 fails. `bh-embeddability-survives-decidable-edge-hnn` stays open.
