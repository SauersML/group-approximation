---
rg: 2
id: rover-nekrashevych-type-one-clopen-stabilizers-are-copies-proof
kind: route
title: Deepen tables until every piece sits in one cone of a fixed decomposition, then transport by a prefix replacement
target: rover-nekrashevych-type-one-clopen-stabilizers-are-copies
requires:
  - rover-nekrashevych-characters-are-sum-invariant
---

Notation as in the claim. For a word `v`, `|v|` is its length. Self-similarity means `g(sw) = g(s) g|_s(w)` with
`g|_s in G` and `|g(s)| = |s|`.

**(T1) Splitting a table piece.** A piece `a w -> b g(w)` equals the `d^L` pieces `a s w -> b g(s) g|_s(w)` with
`|s| = L`. Every table can therefore be replaced by one whose domain cones and range cones all have length at least
any given `M`.

**(T2) Deep cones lie in one piece.** Let `C = ⊔_j c_j C` be a cone partition with every `|c_j| <= M`. Let `vC` be a
cone with `|v| >= M`.

- The point `v 1 1 1 ...` lies in some `c_j C`.
- Since `|c_j| <= |v|`, `c_j` is a prefix of `v`, so `vC ⊆ c_j C`.

**Item 1.**

- Splitting one cone into `d` cones changes the count by `k`.
- Two cone decompositions of `A` both refine, by (T2) and splitting, to the decomposition of `A` into all cones of one
  large length `L`.
- So every cone decomposition of `A` has the same count mod `k`.
- For `h in Γ`, choose by (T1) and (T2) a table of `h` and a cone decomposition of `A` with each cone inside one domain
  piece. A cone `a s C` inside the piece `a w -> b g(w)` maps onto the cone `b g(s) C`. So `h(A)` is a union of the same
  number of cones.

**Item 3.**

1. Take a cone decomposition `𝒟` of `C` refining `{A, C \ A}`. By (T1) and (T2), take a table of `h` whose domain
   cones each lie in `A` or in `C \ A`.
2. Keep the pieces with domain in `A`. Their range cones partition `h(A) = A`.
3. Replace the other pieces by the identity pieces of a cone decomposition of `C \ A`.

This gives a table for `h_A`.

**Item 2.** Write `A = ⊔_{i=1}^n u_i C` with `n = 1 + tk`. Split the root cone `t` times to get a cone partition
`C = ⊔_{i=1}^n v_i C`. Put `φ(u_i w) = v_i w`.

*`φ Γ_A φ^{-1} ⊆ Γ`.* Let `h in Γ_A`. Let `M` exceed every `|u_i|` and the lengths of a fixed cone decomposition of
`C \ A`. By (T1), take a table of `h` whose domain and range cones have length `>= M`. By (T2):

- every domain cone lies in one `u_i C` or in `C \ A`;
- every range cone of a piece with domain in `A` lies in `h(A) = A`, hence in one `u_{i'} C`.

Such a piece reads `u_i s w -> u_{i'} s' g(w)`. Then `φ h φ^{-1}(v_i s w) = v_{i'} s' g(w)`.

- The cones `v_i s C` partition `C`, because the `u_i s C` partition `A`.
- The cones `v_{i'} s' C` partition `C`, because `h|_A` is a bijection of `A`.

So `φ h φ^{-1}` has a table and lies in `Γ`.

*`φ^{-1} Γ φ ⊆ Γ_A`.* Symmetrically, for `k' in Γ` take a table of `k'` with cones inside single `v_i C`. Conjugating
gives pieces `u_i s w -> u_{i'} s' g(w)` on `A`. Adding identity pieces on a cone decomposition of `C \ A` gives a table
of `φ^{-1} k' φ ∪ id_{C \ A}`, which lies in `Γ_A`.

Conjugation is a homomorphism, and these two maps are mutually inverse, so `Γ_A ≅ Γ`.

**Item 4.**

- `Γ_P` permutes the `n` blocks. The kernel of `Γ_P -> Sym(n)` is `K_P`, so `|Γ_P : K_P| <= n!`.
- Elements supported in disjoint sets commute, and `Γ_{B_i} ∩ Π_{j != i} Γ_{B_j} = 1`.
- For `h in K_P`, item 3 gives `h_{B_i} in Γ_{B_i}` and `h = h_{B_1} ⋯ h_{B_n}`.

So `K_P` is the internal direct product. With item 2, `K_P ≅ Γ^n` when every block has type 1.

**Item 5.** Let `(B_i)` and `(B'_i)` be two ordered partitions into type-1 sets.

1. Decompose `B_i` into `n_i` cones and `B'_i` into `n'_i` cones. Then `n_i ≡ n'_i ≡ 1 mod k`.
2. Split cones in the side with fewer cones until `n_i = n'_i`. Each split adds `k`.
3. Match cones bijectively inside each `i`, and let `f` be the prefix replacement `c w -> c' w`.

Then `f in V_d` (a table with all `g_i = 1`) and `f(B_i) = B'_i`.

**Item 6.**

- `A` contains a cone `uC` with `u` nonempty, and `g_(u) in Γ_A`.
- By `rover-nekrashevych-characters-are-sum-invariant`, item 2, `Φ(g_(u)) = χ(g)` for the character `χ` of `G`
  corresponding to `Φ`. The correspondence is a linear isomorphism, so `χ != 0`.
- Pick `g` with `χ(g) != 0`. ∎
