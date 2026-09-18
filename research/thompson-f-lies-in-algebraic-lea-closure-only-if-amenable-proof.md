---
rg: 2
id: thompson-f-lies-in-algebraic-lea-closure-only-if-amenable-proof
kind: route
title: Primality of F under extensions, products, local embeddings and tree actions gives the closure obstruction by transfinite induction
target: thompson-f-lies-in-algebraic-lea-closure-only-if-amenable
requires:
  - thompson-f-has-no-free-subgroups
  - thompson-f-is-lea-only-if-amenable
---

**Imports (trust surface).**
- (I1) Cannon--Floyd--Parry, *Introductory notes on Richard Thompson's groups*, Thm 4.3: every nontrivial
  normal subgroup of `F` contains `F'`. The same import is pinned in `thompson-f-is-lea-only-if-amenable-proof`.
- (I2) CFP Thm 4.1 and Lemma 4.4. `F'` is the set of elements of `F` that are the identity near `0`
  and near `1`. For dyadic `a < b`, `F_[a,b]`, the elements supported in `[a,b]`, is isomorphic to `F`.
  So `F_[1/4,3/4] ≤ F'` is a copy of `F`.
- (I3) `F` is finitely presented, as `⟨x_0, x_1 | R_1, R_2⟩`.
- (I4) Brin--Squier: `F` has no nonabelian free subgroup (`thompson-f-has-no-free-subgroups`).
- (I5) Trees, from Serre, *Trees*, §I.4 and §I.6.5.
  - (a) The Bass--Serre tree of a graph of groups: `π_1` acts without inversions, and vertex
    stabilizers are the conjugates of vertex groups.
  - (b) A finitely generated group acting without inversions, all of whose elements are elliptic,
    fixes a vertex.
  - (c) The Tits alternative for trees (Pays--Valette 1991; Culler--Morgan 1987). If a group `Γ` acts
    without inversions and contains a hyperbolic element, then `Γ` fixes an end, or `Γ` preserves a
    line, or `Γ` contains a nonabelian free subgroup.
- (I6) Graph products (Green; see Hsu--Wise). Let `Γ` be a finite simplicial graph and `v` a vertex
  whose star `st(v)` is not all of `Γ`. Then `G_Γ = G_(Γ∖v) *_(G_lk(v)) G_st(v)`. If `Γ` is
  complete, `G_Γ` is the direct product of the vertex groups.

Throughout, `K` denotes a subgroup of some group with `K ≅ F`, and `K'` is its derived subgroup.
By (I1)–(I2) transported to `K`:
- (P1) every nontrivial normal subgroup of `K` contains `K'`;
- (P2) `K'` contains a subgroup `K_2 ≅ F`, which is finitely generated.

## Lemma A (homomorphisms)

*If `ψ : K → H` is a homomorphism with `ψ(c_K) ≠ 1`, where `c_K ∈ K'` is the image of `c = [x_0,x_1]`,
then `ψ` is injective.*

`ker ψ` is normal in `K` and misses `c_K ∈ K'`. So `ker ψ ⊉ K'`, and by (P1) `ker ψ = 1`.

## Lemma B (extensions)

*If `K ≤ G` and `N ⊴ G`, then `G/N` or `N` contains a copy of `F`.*

`K ∩ N ⊴ K`.
- If `K ∩ N = 1`, the quotient map is injective on `K`, so `K ≅ KN/N ≤ G/N`.
- Otherwise `K ∩ N ⊇ K'` by (P1), and `N ⊇ K_2 ≅ F` by (P2).

## Lemma C (direct products)

*If `K ≤ ∏_(i∈I) G_i` (restricted or unrestricted), then some `G_i` contains a copy of `F`.*

Let `p_i` be the coordinate projections. Then `∩_i ker(p_i|K) = 1`. If every `ker(p_i|K)` were
nontrivial, each would contain `K'` by (P1), and so `K' = 1`. That is false, since `F` is nonabelian.
So some `p_i|K` is injective.

## Lemma D (local embeddings)

*If `G` contains `K` and is locally embeddable into a class `𝒞`, then some `H ∈ 𝒞` contains a copy of `F`.*

Let `S` be the ball in `K` of radius `r ≥ 14`, for the generators corresponding to `x_0, x_1`.
- Every prefix of `R_1`, `R_2` and `c` lies in `S`.
- A local embedding `φ : S → H`, injective and multiplicative on `S`, extends to a homomorphism
  `ψ : K → H`. The relators map to `φ(e) = e`, as in steps 1--2 of
  `thompson-f-is-lea-only-if-amenable-proof`, and this uses (I3).
- `ψ(c_K) = φ(c_K) ≠ φ(e) = e`, since `φ` is injective on `S`.

So `ψ` is injective by Lemma A.

## Lemma E (trees)

*If `K` acts on a tree `T` without inversions, then some subgroup `K_2 ≅ F` of `K` fixes a vertex.*

`K` is finitely generated. There are three cases.
- **All elements elliptic.** `K` fixes a vertex by (I5b). Take `K_2 = K`.
- **A hyperbolic element, and `K` fixes an end `ξ`.** The Busemann homomorphism `β : Stab(ξ) → Z` is
  nonzero exactly on the hyperbolic elements of `Stab(ξ)`. A hyperbolic element fixes only the two ends
  of its axis, and translates along it. An elliptic element fixing `ξ` fixes a ray to `ξ` pointwise, so
  `β = 0`. `β|K` has abelian image, so `K' ≤ ker β`, and every element of `K'` is elliptic.
- **A hyperbolic element, and `K` preserves a line `L`.** The action gives `ρ : K → Aut(L) ≅ D_∞`. A
  nonabelian subgroup of `D_∞` is infinite dihedral, hence virtually abelian, and `F` is not.
  - So `ρ(K)` is abelian and `ker ρ ⊇ K'`.
  - Then `K'` fixes `L` pointwise, and in particular it is elliptic.
- **Otherwise,** by (I5c) `K` contains a nonabelian free subgroup, contradicting (I4).

In the second and third cases, every element of the finitely generated group `K_2 ≤ K'` from (P2) is
elliptic. So `K_2` fixes a vertex by (I5b).

## Lemma F (graphs of groups and graph products)

1. *If `K ≤ π_1(𝒢)` for a graph of groups `𝒢`, then some vertex group contains a copy of `F`.*
   `π_1(𝒢)` acts on its Bass--Serre tree without inversions (I5a). By Lemma E, some `K_2 ≅ F` fixes a
   vertex, so `K_2 ≤ g G_v g^-1` and `g^-1 K_2 g ≤ G_v`.
2. *If `K ≤ G_Γ`, a graph product, then some vertex group contains a copy of `F`.*
   - **Finite `Γ`.** Induct on the number of vertices, through (I6).
     - If `Γ` is complete, `G_Γ` is a finite direct product, and Lemma C applies.
     - Otherwise `G_Γ` is an amalgam of `G_(Γ∖v)` and `G_st(v)`, both graph products on fewer vertices.
       By item 1 one of them contains a copy of `F`, and induction applies.
   - **Infinite `Γ`.** `G_Γ` is the directed union of `G_Λ` over finite full subgraphs `Λ`. The finitely
     generated `K` lies in one of them.

## Proof of item 1 of the claim

`𝒫` is closed under subgroups trivially.
- **Directed unions.** A finitely generated subgroup lies in some member.
- **(K3)** by Lemma D with `𝒞 = 𝒫`: if `G` contained `F`, some `H ∈ 𝒫` would contain `F`.
- **(K4)** by Lemma B.
- **(K5)** by Lemma C.
- **(K6), (K7)** by Lemma F.

In each case, a group built from groups in `𝒫` that contained `F` would force an input group to
contain `F`.

## Proof of item 2 of the claim

- **If `F` is amenable,** then `F` is LEA, so `F ∈ 𝒦`.
- **Conversely, suppose `F` is not amenable.**
  - *Base case.* Every LEA group lies in `𝒫`. An LEA group containing `F` makes `F` LEA (K1 for LEA),
    hence amenable by `thompson-f-is-lea-only-if-amenable`, a contradiction.
  - *Induction.* Define `𝒦_0 = LEA`. `𝒦_(α+1)` is the class of groups obtained from groups in `𝒦_α`
    by one application of (K1)–(K7), and `𝒦_λ = ∪_(α<λ) 𝒦_α` at limits. The union over all ordinals
    is closed under (K1)–(K7), and contains LEA, so it equals `𝒦`.
  - By item 1 and transfinite induction, `𝒦_α ⊆ 𝒫` for every `α`.
  - So `F ∉ 𝒦`.

For (K3), (K5), (K6) and (K7), which take possibly infinitely many inputs, all inputs lie in a common
`𝒦_α`. ∎

## Calibration

- **Known nonamenable groups in `𝒦` are not F-like.** The Kar--Nikolov amalgams
  `SL_n(Z[1/p]) *_Z SL_n(Z[1/p])` are finitely presented, sofic, not LEA, and lie in `𝒦`. They contain
  free subgroups and have many normal subgroups not containing the derived subgroup. Both (I1) and
  (I4) fail, as they must.
- **The tree step genuinely needs (I4).** `F_2 = Z * Z` acts freely on its Bass--Serre tree, so no
  nontrivial subgroup fixes a vertex. An analogue of Lemma E for a group with free subgroups therefore
  needs another hypothesis. (I4) is used only in Lemma E; Lemmas A--D use only (I1)--(I3).
- **The metric step fails.** The universal sofic group `∏_U Sym(n)/(d=0)` is not in the scope of any
  lemma. A copy of `F` there lifts to almost-homomorphisms only, and Lemma D needs an exact homomorphism
  on the ball.
