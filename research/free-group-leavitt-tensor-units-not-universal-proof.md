---
rg: 2
id: free-group-leavitt-tensor-units-not-universal-proof
kind: route
title: Finite presentation makes the space a tree SFT, tree SFT crossed products have a doubly exponential zero test, and the Leavitt tensor adds one exponential
target: free-group-leavitt-tensor-units-are-not-universal
requires:
  - fp-crossed-products-force-sft-over-any-group
  - free-group-sft-host-units-have-doubly-exponential-wp
  - leavitt-tensor-unit-word-problem-reduces-to-base
artifacts:
  - research/artifacts/fp-crossed-product-shape-free-group-kill-2026-09-17.md
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
---

Let `𝓑` be the class of algebras `LC(X, F_2) ⋊ F_d`, over all `d >= 0` and all
nonempty SFTs `X ⊆ A^(F_d)`.

**Step 1. A doubly exponential zero test on `𝓑`.** This is the table argument of
`free-group-sft-host-units-have-doubly-exponential-wp-proof`, applied to all
elements rather than units. Its steps 2 and 3 are stated for arbitrary elements:
- step 2: "`L_(B_M)(X)` is the set of locally legal patterns, decidable in time
  `O(|A|^((2d+1)^M) * (2d+1)^M * d)`";
- step 3: "Represent `Σ_(g∈B_K) φ_g(x|_(B_M)) u_g` by the table
  `(g, p) -> φ_g(p)` on `B_K × L_(B_M)(X)`. Two tables represent the same element
  iff they agree on the language, since every language pattern occurs in a point
  and the `u_g` are a basis."

Fix a finite generating set `b_1..b_m` of `B`, each a table of radius at most
`R`. A noncommutative polynomial of size `n` has at most `n` monomials, each of
degree at most `n`, so each has a table of radius `(Rn, Rn)`, computed by the
multiplication rule of that step 3. Sum the tables and test whether the result
is `0` on `L_(B_(Rn))(X)`. The time is at most
`n * poly((2d+1)^(Rn)) * |A|^((2d+1)^(Rn)) <= C_B 2^(2^(C_B n))`. So `𝓑` satisfies
the hypothesis of part 2 of `leavitt-tensor-unit-word-problem-reduces-to-base`
with `F(n) = 2^(2^n)`, which is recursive and nondecreasing.

**Step 2. The hard input.** Part 2 of that claim gives a two-generated group `H`
with solvable word problem embedding in no `GL_N(B ⊗ L)` with `B ∈ 𝓑`, `N >= 1`.

**Step 3. Reduction to SFTs.** Let `X` be a nonempty compact totally
disconnected `F_d`-space with `B = LC(X, F_2) ⋊ F_d` finitely presented. `B` is
finitely generated, so by Lemma 6.1 of
`fjc-crossed-product-leavitt-hosts-2026-09-16`, `X` is conjugate to an
`F_d`-subshift. The conjugacy induces an isomorphism of crossed products fixing
the `u_g`, so the subshift crossed product is finitely presented, and by
`fp-crossed-products-force-sft-over-any-group` the subshift is an SFT. Thus
`B ≅ B'` with `B' ∈ 𝓑`, and `GL_N(B ⊗ L) ≅ GL_N(B' ⊗ L)`. By step 2, `H` does not
embed. `∎`
