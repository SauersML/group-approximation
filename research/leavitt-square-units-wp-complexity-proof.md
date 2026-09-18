---
rg: 2
id: leavitt-square-units-wp-complexity-proof
kind: route
title: Slot units, baker scrolling and parity pops make the word problem of (L ⊗ L)^x coNP^⊕P-complete
target: leavitt-square-units-have-conp-parity-p-complete-word-problem
requires:
  - leavitt-square-unit-group-is-fp-simple-and-acyclic
---

Lane proof (bh-free-26), elementary. Standard complexity inputs: Toda 1991
(`PH ⊆ BPP^⊕P`); Papadimitriou--Zachos 1983 (`⊕P^⊕P = ⊕P`); Sipser--Gács--Lautemann
(relativized); Bennett's reversible simulation. None is re-derived here.

## 0. Notation

`L = F_2<s_0,s_1,t_0,t_1 | t_i s_j = δ_ij, s_0t_0 + s_1t_1 = 1>`, `A = L ⊗ L`,
`a_i = s_i ⊗ 1`, `a_i^* = t_i ⊗ 1`, `b_i = 1 ⊗ s_i`, `b_i^* = 1 ⊗ t_i`. For a word
`α = i_1...i_k` put `a_α = a_(i_1) ... a_(i_k)` and `a_α^* = (a_α)^*`. The rule
`a_i ↔ a_i^*`, `b_i ↔ b_i^*` defines an anti-automorphism `*` of `A`, because the relations are
`*`-symmetric.

`A` acts on `M = C(C × C, F_2)`, `C = {0,1}^N`, by
`(a_i f)(iξ, y) = f(ξ, y)`, `a_i f = 0` off `[i] × C`, `(a_i^* f)(ξ, y) = f(iξ, y)`, and the
same in the second coordinate for `b`. The relations hold. `A` is simple (the host node; `L` is
central simple), so this nonzero representation is faithful. A homeomorphism `h` of `C × C`
mapping a finite brick partition onto another by prefix replacement gives the monomial unit
`U_h f = f ∘ h^(-1)`, with `U_(h h') = U_h U_(h')`.

Fix the prefix code `Z = {c, e, d, h} = {00, 01, 10, 11}` in the first coordinate. Words of
`Z` are pairwise incomparable, so `a_u^* a_v = δ_uv` for `u, v ∈ Z`. Put `τ = a_0 + a_1` and
`σ = a_0^* + a_1^* = τ^*`. Then `a_i^* τ = 1`, `σ τ = 0` (characteristic 2), and
`τ a_1^* + a_0 σ = 1`.

## 1. Transvections

For distinct `u, v ∈ Z` and `X ∈ A` put `T(u,X,v) = 1 + a_u X a_v^*`. Since
`(a_u X a_v^*)^2 = a_u X (a_v^* a_u) X a_v^* = 0`, `T(u,X,v)` is an involution.

- **(L1)** If `λ a_u = a_u A` and `a_v^* λ^(-1) = a_v^*`, then `λ T(u,X,v) λ^(-1) = T(u,AX,v)`.
- **(L2)** If `ρ a_u = a_u` and `a_v^* ρ^(-1) = B a_v^*`, then `ρ T(u,X,v) ρ^(-1) = T(u,XB,v)`.

Both follow by expanding `1 + (λ a_u) X (a_v^* λ^(-1))`.

## 2. Letter units for the slot `e`, with hotel `h`

Let `Σ_0 = a_c a_c^* + a_d a_d^*`.

- **(τ)** `λ_τ = a_e τ a_e^* + a_(e0) a_0^* a_h^* + a_h a_1^* a_h^* + Σ_0` and
  `μ_τ = a_e a_1^* a_e^* + a_h a_0 σ a_e^* + a_h a_1 a_h^* + Σ_0`. Direct expansion using
  `τ a_1^* + a_0 σ = 1`, `a_1^* τ = 1`, `στ = 0` and `σ a_0 = 1` gives
  `λ_τ μ_τ = a_e a_e^* + a_h a_h^* + Σ_0 = 1` and `μ_τ λ_τ = 1`. Also `λ_τ a_e = a_e τ`.
- **(a_i)** `λ_(a_0) = a_(e0) a_e^* + a_(e1) a_0^* a_h^* + a_h a_1^* a_h^* + Σ_0` and
  `λ_(a_1) = a_(e1) a_e^* + a_(e0) a_0^* a_h^* + a_h a_1^* a_h^* + Σ_0`. These are monomial
  units: they map `[e] → [ei]`, `[h0] → [e(1-i)]`, `[h1] → [h]`. Also `λ_(a_i) a_e = a_(ei)`.
- **Right letters.** For `B ∈ {σ, a_0^*, a_1^*}` let `ρ_B = ((λ_(B^*))^(-1))^*`. Then
  `a_e^* ρ_B^(-1) = (λ_(B^*) a_e)^* = B a_e^*`.
- **Bijective letters.** For a unit `Q` let `δ_e(Q) = a_e Q a_e^* + (1 - a_e a_e^*)`. This is
  a group homomorphism on units, with `δ_e(Q) a_e = a_e Q` and `a_e^* δ_e(Q) = Q a_e^*`. Put
  `λ_Q = δ_e(Q)` and `ρ_Q = δ_e(Q^(-1))`.

Every letter unit is the identity on the regions `[c] × C` and `[d] × C`. So:
- `λ` satisfies (L1) with `(u,v) = (e,d)`;
- `ρ` satisfies (L2) with `(u,v) = (c,e)`.

## 3. One commutator

Let `L = B_1 ⋯ B_m`, where each `B_i` is `σ`, `a_0^*`, `a_1^*` or a unit, and `R = A_1 ⋯ A_k`,
where each `A_j` is `τ`, `a_0`, `a_1` or a unit. Put

`g_1 = (ρ_(B_m) ⋯ ρ_(B_1)) T(c,1,e) (ρ_(B_m) ⋯ ρ_(B_1))^(-1) = T(c,L,e)` (by L2, applied
`m` times), and

`g_2 = (λ_(A_1) ⋯ λ_(A_k)) T(e,1,d) (λ_(A_1) ⋯ λ_(A_k))^(-1) = T(e,R,d)` (by L1).

With `N_1 = a_c L a_e^*` and `N_2 = a_e R a_d^*` we have `N_1^2 = N_2^2 = 0` and
`N_2 N_1 = a_e R (a_d^* a_c) L a_e^* = 0`, while `N_1 N_2 = a_c L R a_d^*`. Hence
`(g_1 g_2)^2 = (1 + N_1 + N_2 + N_1N_2)^2 = 1 + N_1N_2` in characteristic 2. Every other
square term vanishes, because it contains `N_1^2`, `N_2^2` or `N_2N_1`. So

`[g_1, g_2] = g_1 g_2 g_1 g_2 = 1 + a_c (L R) a_d^*`,  **(★)**

and it equals `1` iff `LR = 0`, since `a_c^*(a_c Y a_d^*)a_d = Y`. Its length over the finite
letter set is `O(m + k + Σ |unit letters|)`.

## 4. Circuits by baker scrolling

The baker unit `Bk = b_0 a_0^* + b_1 a_1^* = U_β`, `β(iξ, y) = (ξ, iy)`, has inverse
`a_0 b_0^* + a_1 b_1^*`. For `π ∈ Sym({0,1}^3)` let `Π_π = Σ_γ a_(π(γ)) a_γ^*`, a permutation
of the first three digits of the first coordinate. Then `Bk^(-r) Π_π Bk^r = U_(β^(-r) π β^r)`
applies `π` to digits `r+1, r+2, r+3` of the first coordinate. The second coordinate is only
used as scratch and is restored.

So NOT, CNOT, Toffoli and adjacent swaps at depth `r` cost `2r + 1` letters from
`Γ_0 = {Bk^(±1), Π_π}`. A gate on arbitrary positions among the first `m` digits is conjugated
by at most `2m` adjacent swaps into consecutive position. Hence a reversible circuit with `s'`
gates on `m` digits is a word of length `O(s' m^2)` over `Γ_0`. It acts as
`U_(π_circ)`, where `π_circ` permutes the first `m` digits of the first coordinate.

**Bennett.** Let `R` be a fan-in-2 AND/OR/NOT circuit of size `s` with inputs
`x ∈ {0,1}^p`, `y ∈ {0,1}^q`. Put `K = s` and `m = K + 1 + q + p`, with the layout: ancillas =
digits `1..K`, `b` = digit `K+1`, then `y`, then `x`. Compute each gate into its own ancilla
(AND by Toffoli; OR by De Morgan; NOT by CNOT and NOT), CNOT the output into `b`, and uncompute
in reverse. This gives a Toffoli circuit of size `O(s)` whose permutation `π_R` satisfies
`π_R(0^K, b, y, x) = (0^K, b ⊕ R(x,y), y, x)`. So `P_R := U_(π_R)` is a word of length
`O(s^3)` over `Γ_0`, and `δ_e(P_R^(±1))` is the same word over `δ_e(Γ_0)`.

## 5. Hardness

Put `X_R = σ^q a_1^* (a_0^*)^K P_R (a_0)^(K+1) τ^q`. For `g ∈ M` and `x ∈ {0,1}^p`:
- `(τ^q g)(y'ζ, ·) = g(ζ, ·)` for all `y'`;
- `F := a_0^(K+1) τ^q g` has `F(0^(K+1) y' ζ, ·) = g(ζ, ·)` and vanishes elsewhere;
- `(P_R F)(z) = F(π_R^(-1) z)` is supported on `{(0^K, R(x,y'), y', x, ξ)}` and equals
  `g(xξ, ·)` there;
- `(a_0^*)^K` then `a_1^*` keep exactly the branches with `R(x,y') = 1`;
- `σ^q` adds over `y'`.

So `(X_R g)(xξ, η) = (⊕_(y') R(x,y')) · g(xξ, η)`. That is, `X_R` is multiplication by
`χ_R(x) = ⊕_y R(x,y)` in the first `p` digits, and `X_R = 0` iff `χ_R ≡ 0`.

`X_R = L R_0` with `L = σ^q a_1^* (a_0^*)^K P_R` (letters `σ`, `a_1^*`, `a_0^*`, `P_R`) and
`R_0 = a_0^(K+1) τ^q` (letters `a_0`, `τ`). By (★),
`W_R := [g_1, g_2] = 1 + a_c X_R a_d^*` is a word over the finite set
`Λ = {T(c,1,e), T(e,1,d)} ∪ {λ, ρ letters} ∪ δ_e(Γ_0)^(±1)`. It has length `O(s^3)` and is
computable in time polynomial in `s`. So `W_R = 1` iff `∀x: ⊕_y R(x,y) = 0`.

**Completeness of the source problem.** `⊕P` is closed under complement, intersection and
Turing reductions (`⊕P^⊕P = ⊕P`), so `NP^⊕P = ∃·⊕P`. For `L ∈ coNP^⊕P`, `w ∈ L` iff
`∀x ⊕_y R'(w,x,y) = 0` for a polynomial-time `R'`, whose circuit `R_w` is computable from `w`.
So `w ↦ W_(R_w)` is a many-one reduction to `WP(Γ)`, and `WP(Γ)` is `coNP^⊕P`-hard.

## 6. Upper bound

Let `W` be a word of length `ℓ` over any finite set of units of `A`. Each unit is a fixed
finite sum of monomials `a_(α') b_(β') b_β^* a_α^*`; a product of monomials is `0` or a
monomial whose lengths add. So `X = W - 1` is a sum of monomials of lengths `≤ D = cℓ`.
Refine using `Σ_i a_i a_i^* = 1 = Σ_i b_i b_i^*` on the right, so that every `|α| = |β| = D`.
Then `X = Σ_(α,β) Y_(αβ) a_α^* b_β^*`, where `Y_(αβ) = Σ c a_(α') b_(β')` has
`|α'|, |β'| ≤ 2D`, and `X a_α b_β = Y_(αβ)`. So `X = 0` iff every `Y_(αβ) = 0`.

**Witness lemma.** Put `ε = η = 0 1^(3D) 0`. For `|α'|, |α''| ≤ 2D` with `α' ≠ α''`, the
cylinders `[α'ε]` and `[α''ε]` are disjoint. If `|α'| = |α''|` this is clear. Otherwise a
proper-prefix relation would put the run `1^(3D)` of `ε` across the leading `0` of the other
`ε`, which is impossible. The same holds for bricks. So
`Y_(αβ) 1_([ε] × [η]) = Σ c 1_([α'ε] × [β'η])` vanishes iff every coefficient does, iff
`Y_(αβ) = 0`.

Hence `W = 1` iff for all `α, β ∈ {0,1}^D` and all points `z` whose prefixes have length
`≤ 5D + 2` (tails `0^∞`), `(X f_(αβ))(z) = 0`, where `f_(αβ) = 1_([αε] × [βη])`. Here
`(W f)(z) = Σ` over choices of one monomial per letter of `(m_1 ⋯ m_ℓ f)(z)`, and each term is
evaluated in polynomial time by tracking `z` backwards through prefix conditions. So each test
is a `⊕P` predicate, and `WP ∈ ∀·⊕P = coNP^⊕P`.

## 7. Conclusions

Sections 5 and 6 give `coNP^⊕P`-completeness for `Γ = <Λ>`, and the upper bound for every
finitely generated subgroup of `A^x`. `H = A^x` is finitely generated and contains `Λ`, and
changing finite generating sets is a linear substitution. So `WP(H)` is `coNP^⊕P`-complete,
with finite presentation and simplicity of `H` taken from
`leavitt-square-unit-group-is-fp-simple-and-acyclic`.

If `WP(H) ∈ coNP`, then `⊕P ⊆ coNP`, so `PH ⊆ BPP^⊕P ⊆ BPP^NP ⊆ Σ_3^p` (Toda;
Sipser--Gács--Lautemann relativized).

## Checks

- **Calibration.** `q = 0` gives `W = 1` iff `R` is unsatisfiable, the coNP-hardness known
  for `2V ≤ H` (Birget). `p = 0` gives the parity of `#SAT`.
- **Where one tensor factor fails.** Without `Bk`, the depth-`r` gate `Bk^(-r) Π Bk^r` is
  replaced by `δ^r(Π)`, whose word length in `L^x` grows like `2^r`. The polynomial bound
  then fails. So the hardness proof does not transfer to `L^x`.
