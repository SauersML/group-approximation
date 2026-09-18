---
rg: 2
id: alternating-v-full-group-wp-computes-sft-language
kind: claim
title: The word problem of the full group of V times Λ ⋉ X decides the pattern language of X through polynomial-length nested commutators
distinct_from:
  full-group-word-problem-iff-recursive-language: that is Grigorchuk--Medynets' decidability equivalence for derived full groups of minimal Z-subshifts, with no complexity bound and no V factor; this is a length-polynomial many-one reduction of the pattern language of an arbitrary subshift over an arbitrary finitely generated group to the word problem of any finitely generated group containing a fixed finitely generated subgroup of F(G_V × (Λ ⋉ X)).
  subshift-elementary-group-word-problem-equals-language: that computes the word problem of elementary groups over crossed-product rings from the language; this is the opposite direction, a lower bound, for Cantor full groups, and it is quantitative.
  half-finite-shift-envelope-wp-computes-generators: that lower-bounds the word problem of permutation envelopes on N by the cost of evaluating their generators; this lower-bounds full groups of transformation groupoids by the cost of their subshift language, with no generator of the group being hard to evaluate.
  twisted-brin-thompson-wp-equals-actor-orbit-problem: that is an exact equivalence for twisted Brin--Thompson groups and actor orbits; this is a one-sided reduction for Nekrashevych full groups of V times a transformation groupoid.
---

**ESTABLISHED** by `alternating-v-full-group-wp-computes-sft-language-proof`.

**Setting.**
- `Λ` is a group with finite symmetric generating set `S`, and `|g|` is word
  length.
- `X ⊆ A^Λ` is a nonempty subshift, with `(λx)(g) = x(λ^(-1) g)`. No finite
  type, minimality or freeness is assumed.
- `G_V` is the groupoid of germs of Thompson's group `V` on `C = {0,1}^N`, and
  `T = G_V × (Λ ⋉ X)`. `F(T)` and `A(T)` are its topological and alternating
  full groups.
- For `U ⊆ X` clopen and a permutation `ρ ∈ S_5`, `ρ_U ∈ F(T)` acts by
  `(c, x) -> (ρ̂(c), x)` for `x ∈ U`, and trivially for `x ∉ U`. Here `ρ̂ ∈ V`
  permutes the cylinders `[0], [10], [110], [1110], [1111]` by prefix
  replacement.
- `φ_λ ∈ F(T)` is `(c, x) -> (c, λx)`.
- `E = { φ_s : s ∈ S } ∪ { ρ_(U_a) : ρ ∈ A_5, a ∈ A }`, with
  `U_a = { x : x(e) = a }`. Let `Q = <E> ≤ F(T)`.

**Theorem.**
1. `Q ≤ A(T)`.
2. There is a polynomial-time algorithm with the following input and output.
   - Input: a pattern `p : F -> A` on a finite `F ⊆ Λ`, `|F| = m >= 1`, with each
     `g ∈ F` given by an `S`-word of length at most `r`.
   - Output: a word `W(p)` over `E^(±1)` of length at most `4 m^2 (2r + 1)`.
   - Property: `W(p) = 1` in `F(T)` iff `p` occurs in no configuration of `X`.
3. **Complexity transfer.** Let `Γ ⊇ Q` be a finitely generated group, for
   instance `A(T)` when it is finitely generated. Let `R` be recursive and
   non-decreasing with `R(n) >= n`. If the word problem of `Γ` is in `F(R)`,
   then the pattern language of `X` on inputs of size `n = m + r` is in `F(R_4)`,
   where `R_4(n) = R(n^4)`. For `Λ = Z^2` with `S = {±e_1, ±e_2}`, the row
   language (`m = n`, `r <= n`) is in `F(R_4)`.

**Use.** With `minimal-free-z2-sfts-have-arbitrarily-hard-row-languages` and
premise (P2) this gives finitely presented simple groups beyond every recursive
bound (route
`arbitrarily-complex-fp-simple-via-hard-minimal-sft-v-full-groups`). It also
shows that, among the hosts `A(G_V × (Λ ⋉ X))` of
`boone-higman-via-v-times-aperiodic-sft-full-groups`, word problems are at least as hard as
the subshift languages, up to the polynomial substitution `n -> n^4`. The `V`
factor absorbs none of the language's complexity. The converse upper bound
(word problem from the language) is not claimed here.
