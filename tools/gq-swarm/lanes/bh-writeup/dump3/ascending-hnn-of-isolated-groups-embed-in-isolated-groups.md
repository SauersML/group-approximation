---
rg: 2
id: ascending-hnn-of-isolated-groups-embed-in-isolated-groups
kind: claim
title: Groups embeddable in isolated groups are closed under finite products and finite extensions, and contain every ascending HNN extension of an isolated group
distinct_from:
  every-decidable-group-embeds-in-an-isolated-group: that is CGP Question 4 for all decidable groups; this gives permanence properties of the class of groups embedding in isolated groups, and a criterion for the Baumslag--Gersten group.
  mif-free-product-automorphism-ascending-hnn-is-pbh: that puts mapping tori of finitely presented simple MIF groups in the permutational Boone--Higman class; this puts every ascending HNN extension of every isolated group, including non-MIF bases and non-surjective endomorphisms, in the weaker isolated-embeddable class.
  outer-extensions-of-fp-simple-groups-are-isolated: that is CGP's outer-extension corollary with a simple kernel; this covers ascending HNN extensions, which are not extensions of the base, and the case of finite outer order.
  limits-of-isolated-groups-basic-closure: that is about limits of isolated groups (CGP Question 1); this is about subgroups of isolated groups (CGP Question 4).
---

**ESTABLISHED** through `ascending-hnn-of-isolated-groups-proof`. Lane proof (bh-free-05),
elementary, not reviewed. No priority claimed.

Terms follow Cornulier--Guyot--Pitsch, as quoted in `fp-simple-groups-are-isolated`. A group
is isolated iff it is finitely presented and finitely discriminable, i.e. some finite
`F ⊂ G − {1}` meets every nontrivial normal subgroup. Let `𝓘` be the class of finitely
generated groups that embed in an isolated group. CGP Question 4 asks whether `𝓘` contains
every finitely generated group with solvable word problem.

## Statement

1. **Products.** If `J_1, J_2` are isolated, so is `J_1 × J_2`. Hence `𝓘` is closed under
   finite direct products, and `Z ∈ 𝓘` (since `Z <= V`).
2. **Finite extensions.** If `J` is isolated and `k >= 1`, then `J ≀ S_k = J^k ⋊ S_k` is
   isolated. Hence `𝓘` is closed under finite extensions: if `G ∈ 𝓘` and `[G' : G] < ∞`,
   then `G' ∈ 𝓘`.
3. **Ascending HNN extensions of isolated groups.** Let `I` be isolated, let `α : I -> I` be
   an injective endomorphism, let `Γ = I*_α = < I, t | t x t^-1 = α(x) >`, and let
   `B = ⋃_k t^-k I t^k`. Then exactly one of the following holds.
   - (A) `C_Γ(B) ⊆ B`. Then `Γ` is itself isolated, with the same discriminating set as `I`.
   - (B) Some `c = y t^k`, with `y ∈ B` and `k >= 1`, centralizes `B`. Then `B ≅ I`, `Γ`
     contains `B × <c>` with index `k`, and `Γ ∈ 𝓘`.

   In particular `I*_α ∈ 𝓘` for every isolated `I` and every injective endomorphism `α`.
   For an automorphism `α`, (A) says that no nonzero power of `α` is inner, which is CGP's
   outer-extension corollary. (B) is the case of finite outer order.
4. **Criterion by homomorphisms.** Let `N ⊴ G` with `G/N ∈ 𝓘`. Then `G ∈ 𝓘` iff some
   homomorphism from `G` to an isolated group is injective on `N`. Proof: use
   `G -> I × G/N`.

## Consequences

- **Mapping tori and ascending HNN extensions of finitely presented simple groups.** For every
  finitely presented simple `S` and every injective endomorphism `α` of `S`, surjective or
  not, `S*_α ∈ 𝓘`.
  - The Boone--Higman analogue on main is special-case only. `mif-free-product-automorphism-ascending-hnn-is-pbh`
    (lane proof) needs `α` to be the restriction of an automorphism of `M * F_m`, for a finitely
    presented simple MIF group `M` containing `S`. `pbh-class-closed-under-relative-holomorphs` (T)
    needs `S ∈ B_A` and `α` inner.
  - When `M = S` the first condition forces `α` to be surjective, by Kurosh. Item 3 needs no MIF
    hypothesis, no overgroup and no surjectivity.
  - Also covered: iterated ascending HNN towers in which every step is in case (A).
- **The Baumslag--Gersten group.** Write `BG = < a, t | a^(a^t) = a^2 >` and
  `C = ncl(a) = ⋃ <a_-n, ..., a_n>`, where `a_n = t^n a t^-n` and
  `a_(n+1) a_n a_(n+1)^-1 = a_n^2`. Let `σ` be the shift `a_n -> a_(n+1)`, so
  `BG = C ⋊_σ Z`. Then the following are equivalent:
  - (i) `BG ∈ 𝓘`, i.e. `BG` embeds in an isolated group;
  - (ii) some homomorphism from `BG` to an isolated group is injective on `C`;
  - (iii) `C` embeds in an isolated group `I` such that `σ` extends to an automorphism of `I`.

  (iii) ⇒ (i) is item 3 applied to `I ⋊ Z`. (i) ⇒ (iii) takes the extension to be
  conjugation by `t`. (ii) ⟺ (i) is item 4. For Boone--Higman no criterion this clean is
  available, since closure of the Boone--Higman class under `× Z` is open
  (`bh-class-free-products-iff-joint-embedding-and-free-z`). `BG ∈ 𝓘` itself stays OPEN:
  every finite quotient and every almost-automorphism image of `BG` kills `a`
  (`baumslag-gersten-group-satisfies-boone-higman`), so (ii) needs an infinite isolated
  target that no known host supplies.
