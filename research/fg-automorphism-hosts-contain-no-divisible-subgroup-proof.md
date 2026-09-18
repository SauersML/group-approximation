---
rg: 2
id: fg-automorphism-hosts-contain-no-divisible-subgroup-proof
kind: route
title: Characteristic finite-index subgroups for Aut(Γ); finite rings of points for Aut(X); divisibility dies in finite quotients
target: fg-automorphism-hosts-contain-no-divisible-subgroup
requires: []
---

Direct proof. Lane proof, not independently reviewed.

## Step 0: residually finite groups have no nontrivial divisible subgroup

Let `D` be a divisible abelian group and `f : D -> F` a homomorphism to a finite
group. The image `f(D)` is a finite divisible abelian group; multiplication by
`|f(D)|` is both surjective and zero on it, so `f(D) = 1`. Hence `D` lies in every
finite-index normal subgroup of any group containing it. In a residually finite group
these intersect trivially, so `D = 1`. Subgroups of residually finite groups are
residually finite. This is the root's obstruction O1.

## Step 1: (a), after Baumslag

Let `Γ` be finitely generated and residually finite. For `k >= 1` let `Γ_k` be the
intersection of all subgroups of index at most `k`.
- A subgroup of index `j` is the stabilizer of a point in a transitive action on
  `j` points. A finitely generated group has finitely many homomorphisms to `S_j`, so
  it has finitely many subgroups of index at most `k`. Hence `[Γ : Γ_k]` is finite.
- Automorphisms permute the subgroups of index at most `k`, so `Γ_k` is
  characteristic. Every automorphism therefore induces one of the finite group
  `Γ/Γ_k`. This gives homomorphisms `Aut(Γ) -> Aut(Γ/Γ_k)` with finite targets.
- A finite-index normal subgroup `N` contains `Γ_{[Γ:N]}`. Since `Γ` is residually
  finite, `⋂_k Γ_k = 1`.
- Let `α ≠ id` and pick `g` with `α(g) ≠ g`. Then `g^{-1} α(g) ≠ 1`, so it lies
  outside some `Γ_k`, and `α` acts nontrivially on `Γ/Γ_k`.

So the finite quotients `Aut(Γ) -> Aut(Γ/Γ_k)` separate points.

## Step 2: (b), after Bass--Lubotzky

Let `Γ = <γ_1, ..., γ_r> <= Aut_K(X)`, with `X` separated and of finite type over
`K`.

**Spreading out** (the standard limit arguments of EGA IV §8, and generic flatness,
EGA IV §6; section numbers not re-checked). There are:
- a finitely generated `Z`-subalgebra `R ⊆ K`, which is a domain;
- a separated `R`-scheme `X_R` of finite type, flat over `R`, with
  `X_R ⊗_R K ≅ X`;
- `R`-automorphisms `γ_{i,R}` of `X_R` whose base changes are the `γ_i`.

Take `R` large enough that `γ_{i,R}^{-1}` is also defined, and localize so that
`X_R` is flat.

**Base change is injective on `Aut_R(X_R)`.** Let `δ` be an `R`-automorphism with
`δ_K = id`.
- Its equalizer with the identity is a closed subscheme `E ⊆ X_R`, because `X_R`
  is separated, and `E` contains the generic fibre.
- `X_R` is flat over the domain `R`, so its structure sheaf has no `R`-torsion.
  Hence the generic fibre is schematically dense, so `E = X_R` and `δ = id`.

So `<γ_{i,R}>` maps isomorphically onto `Γ`, and `Γ` acts faithfully on `X_R` by
`R`-automorphisms.

**Finite `Γ`-sets.** For a finite `R`-algebra `B`, `Γ` acts on
`X_R(B) = Hom_R(Spec B, X_R)` by composition. This set is finite:
- `B` is a finite product of finite local rings `B_l`;
- each map `Spec B_l -> X_R` factors through one of finitely many affine charts
  `Spec A_j`;
- each `A_j` is finitely generated, so `Hom(A_j, B_l)` is finite.

**Separation.** Let `γ ≠ 1` in `Γ`, acting on `X_R`.
- Let `Z ⊊ X_R` be the equalizer of `γ` and the identity, a proper closed
  subscheme. Choose an affine open `U = Spec A` on which `Z` is cut out by a nonzero
  ideal `I`, and some `b ∈ I`, `b ≠ 0`.
- `A` is a finitely generated `Z`-algebra, so it is Noetherian and Jacobson, and its
  residue fields at maximal ideals are finite.
- `Ann(b)` is proper, so it lies in a maximal ideal `n`, and `b/1 ≠ 0` in `A_n`.
- By Krull's intersection theorem there is a `k` with `b ∉ n^k A_n`. Let `J` be the
  preimage of `n^k A_n` in `A`. It contains `n^k`, and `A/n^k` is finite: it is
  filtered by the finite-dimensional `A/n`-spaces `n^i/n^{i+1}` over the finite field
  `A/n`. So `B := A/J` is a finite ring and `b ∉ J`.
- The point `x : Spec B -> U ⊆ X_R` does not factor through `Z`, since `I ⊄ J`. By
  the universal property of the equalizer, `γ ∘ x ≠ x`.

So `γ` acts nontrivially on the finite `Γ`-set `X_R(B)`, and `Γ` is residually
finite.

## Step 3: (c)

Combine Steps 1 and 2 with Step 0. For `n >= 2`, the unipotent matrices
`[[1,q],[0,1]]` (`q ∈ Q`), embedded in the upper left corner, give a copy of `(Q,+)`
inside `GL_n(Q)`, `SL_n(Q)`, `B_n(Q)` and the image of `SL_n(Q)` in `PSL_n(Q)`.
Translations give one inside `Aff(Q)`, and the centre gives one inside `U_3(Q)`.
