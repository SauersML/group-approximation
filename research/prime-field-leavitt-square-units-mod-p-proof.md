---
rg: 2
id: prime-field-leavitt-square-units-mod-p-proof
kind: route
title: Characteristic-free slot units and mod-p pops make the word problem of (L_p ⊗ L_p)^x / F_p^x complete for ∀·Mod_pP
target: leavitt-square-units-mod-p-complete-word-problem
requires:
  - prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre
  - prime-field-leavitt-tensor-powers-have-trivial-k-theory
  - leavitt-square-units-wp-complexity-proof
---

Lane proof (bh-free-26), elementary. Notation is that of `leavitt-square-units-wp-complexity-proof`
(below, "the `F_2` route"), over `F_p` in place of `F_2`. So `R = L_p ⊗ L_p` has generators
`a_i, a_i^*, b_i, b_i^*`, with the prefix code `Z = {c,e,d,h} = {00,01,10,11}` in the first
coordinate. `τ = a_0 + a_1` and `σ = a_0^* + a_1^* = τ^*`. The action on `M = C(C × C, F_p)`
is given by the same formulas. The involution `*` is an anti-automorphism in every
characteristic, because the relations are `*`-symmetric.

Each step below says what changes from the `F_2` route.

## 1. Transvections (changed: inverses and commutator sign)

For distinct `u, v ∈ Z`, `T(u,X,v) = 1 + a_u X a_v^*` is a unit with inverse
`1 - a_u X a_v^*`, because `(a_u X a_v^*)^2 = 0`. Rules (L1) and (L2) of the `F_2` route hold
verbatim.

**Steinberg commutator.** Let `N_1 = a_c L a_e^*` and `N_2 = a_e R' a_d^*`. Then
`N_1^2 = N_2^2 = N_2 N_1 = 0` and `N_1 N_2 = a_c L R' a_d^*`. Expanding
`(1+N_1)(1+N_2)(1-N_1)(1-N_2)` term by term, every product containing `N_1^2`, `N_2^2` or
`N_2N_1` vanishes. What remains is

`1 + N_1 + N_2 + N_1N_2 - N_1 - N_2 + N_1N_2 - N_1N_2 = 1 + N_1 N_2.`

So, with `g_1 = 1 + N_1` and `g_2 = 1 + N_2`,

`g_1 g_2 g_1^(-1) g_2^(-1) = 1 + a_c (L R') a_d^*`   (★_p)

in every characteristic.

## 2. Letter units (changed: the superposition letter)

The monomial letters `λ_(a_0)`, `λ_(a_1)` of the `F_2` route are monomial units in every
characteristic, with `λ_(a_i) a_e = a_(ei)`, and they are the identity on `[c] × C` and
`[d] × C`. The same holds for `δ_e(Q) = a_e Q a_e^* + (1 - a_e a_e^*)`. That map is a group
homomorphism on units, with `δ_e(Q) a_e = a_e Q` and `a_e^* δ_e(Q) = Q a_e^*`.

**New τ-letter.** Put `u_0 = 1 + a_1 a_0^*`, a unit with inverse `1 - a_1 a_0^*`. Then
`u_0 a_0 = a_0 + a_1 = τ`. Set

`λ_τ = δ_e(u_0) λ_(a_0).`

- `λ_τ a_e = δ_e(u_0) a_e a_0 = a_e u_0 a_0 = a_e τ`.
- `a_d^* λ_τ^(-1) = a_d^* λ_(a_0)^(-1) δ_e(u_0^(-1)) = a_d^*`, since both factors are the
  identity on `[d] × C`.
- The same computation with `a_c` gives `a_c^* λ_τ^(-1) = a_c^*`.

So `λ_τ` satisfies (L1) with `(u,v) = (e,d)`. This replaces the characteristic-two formula;
over `F_2` either one works.

**Right letters.** As before, `ρ_B = ((λ_(B^*))^(-1))^*` for `B ∈ {σ, a_0^*, a_1^*}`, and
`ρ_Q = δ_e(Q^(-1))` for units `Q`. Then `a_e^* ρ_B^(-1) = (λ_(B^*) a_e)^* = B a_e^*`. Also
`ρ_B a_c = (a_c^* λ_(B^*)^(-1))^* = a_c`. So (L2) holds with `(u,v) = (c,e)`.

## 3. Circuits (unchanged)

Baker scrolling `Bk = b_0 a_0^* + b_1 a_1^*` and the permutations `Π_π` are monomial units.
So §4 of the `F_2` route gives, for a circuit `Q(x,y)` of size `s`, a word of length `O(s^3)`
for `P_Q = U_(π_Q)`, where `π_Q(0^K, b, y, x) = (0^K, b ⊕ Q(x,y), y, x)` with `b ⊕ Q` computed
in `{0,1}`.

## 4. Counting mod p

Let `X_Q = σ^q a_1^* (a_0^*)^K P_Q a_0^(K+1) τ^q`. The computation of §5 of the `F_2` route
goes through unchanged up to the last step. There `σ^q` sums the `2^q` branches in `F_p`:

`(X_Q g)(xξ, η) = N_Q(x) · g(xξ, η),   N_Q(x) = #{y : Q(x,y) = 1} mod p.`

So `X_Q` is multiplication by the function `x ↦ N_Q(x)` of the first `p'` digits (`p'` = the
length of `x`). It is `0` iff `N_Q ≡ 0` mod `p`, and if `N_Q(x_0) ≠ 0`, then
`X_Q 1_([x_0] × C) ≠ 0`.

Conjugating `T(c,1,e)` by the `ρ`-letters of `L = σ^q a_1^* (a_0^*)^K P_Q`, and `T(e,1,d)` by the
`λ`-letters of `R' = a_0^(K+1) τ^q`, gives `g_1 = T(c,L,e)` and `g_2 = T(e,R',d)`. By (★_p),

`W_Q = g_1 g_2 g_1^(-1) g_2^(-1) = 1 + a_c X_Q a_d^*`.

This is a word of length `O(s^3)` over the finite set
`Λ_p = {T(c,1,e), T(e,1,d)} ∪ {λ, ρ letters} ∪ δ_e(Γ_0)^(±1)`, computable in polynomial time.
Put `Γ_p = <Λ_p>`.

**Projective detection.** Suppose `1 + N = k·1` with `N = a_c X_Q a_d^*` and `k ∈ F_p^x`. Then
`N = (k-1)·1`, and `N^2 = 0` gives `(k-1)^2 = 0` in `F_p`, so `k = 1` and `N = 0`. Hence
`W_Q ∈ F_p^x` iff `W_Q = 1` iff `X_Q = 0` iff `∀x N_Q(x) ≡ 0`. Only the words `W_Q` are
used, so nothing is claimed about `Γ_p ∩ F_p^x` in general.

**Reduction.** Take `L ∈ ∀·Mod_pP`, given by `Q'(w,x,y)`. The map `w ↦ W_(Q'_w)` is a
polynomial-time many-one reduction from `L` to the word problem of the image of `Γ_p` in
`P_p`, hence to `WP(P_p)` after substituting fixed words for the letters.

## 5. Upper bound

Let `W` be a word of length `ℓ` over a finite set of units of `R`. §6 of the `F_2` route applies
verbatim over `F_p`:
- the monomial expansion;
- the refinement to `|α| = |β| = D`;
- the witness lemma with `ε = η = 0 1^(3D) 0`. It uses only disjointness of cylinders, not
  the characteristic, and it needs no faithfulness of `M`, since a vanishing test value forces
  every coefficient of `Y_(αβ)` to be `0`.

So `W = k·1` iff for all `α, β ∈ {0,1}^D` and all points `z` of prefix length `≤ 5D+2`,

`(W f_(αβ))(z) - k f_(αβ)(z) = 0`.

Here `(W f)(z) = Σ` over choices of one monomial per letter of `c_path · f(ψ_path(z))`. Each
term is computable in polynomial time, and `c_path ∈ F_p` is a product of fixed coefficients.
So `(W f)(z) = Σ_path c_path f(ψ_path(z))` is a count mod `p` over polynomially checkable
paths, each valid path contributing `c_path ∈ {0..p-1}` copies. The test `(W f)(z) = k f(z)` is then a `coMod_pP` predicate, which is a `Mod_pP`
predicate for prime `p`.

- For `R^x`, take `k = 1`: `WP ∈ ∀·Mod_pP`.
- For `R^x / F_p^x`, `W` is trivial iff `W = k·1` for one of the `p-1` values of `k`. A
  disjunction of constantly many `∀·Mod_pP` predicates is again one, as
  `∀x A(x) ∨ ∀x' B(x') = ∀x,x' (A(x) ∨ B(x'))`, and `Mod_pP` is closed under `∨`.

## 6. Conclusion

§§4--5 give `∀·Mod_pP`-completeness of `WP(P_p)`. Finite presentation and simplicity of `P_p`
are part 1 of the target (imports as stated there).
