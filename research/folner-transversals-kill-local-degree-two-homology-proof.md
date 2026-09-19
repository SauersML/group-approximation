---
rg: 2
id: folner-transversals-kill-local-degree-two-homology-proof
kind: route
title: A 2-cycle of the universal cover supported on a transversal is a boundary there, so it dies in every finite cover; rank-nullity on the transversal leaves only the Følner boundary as room for local H_2, and integrality of chi turns the leftover into a race between relator depth and Følner radius
target: folner-transversals-kill-local-degree-two-homology
requires:
  - rf-weak-bass-defect-is-degree-two-approximation-defect
---

Notation as in the target. Chains are left modules, and a chain `Σ_r a_r e_r` with `a_r ∈ k[K]`
is written as a row vector `a`. Boundary maps act by right multiplication by matrices.

## 1. The chain model

Let `X` be a `K(K, 1)` with one 0-cell, 1-cells `S`, one 2-cell for every element of `R`, and
cells of dimension `>= 3`. Such an `X` exists: attach cells of dimension `>= 3` to the
presentation complex to kill `π_{>=2}`. For `L >= 0`, let `Y_L ⊂ X^{(2)}` be the subcomplex whose
2-cells are the relators of length `<= L`. So `Y_L` is the presentation complex of `Γ_L`, with
`c = |R_{≤L}|` 2-cells.

The cellular chains of the universal cover `X̃` with coefficients in `k` are
`C_2(X̃) ⊇ k[K]^c`, `C_1 = k[K]^n` and `C_0 = k[K]`. On `k[K]^c` we have `∂_2(a) = aJ`, where
`J ∈ M_{c×n}(k[K])` is the Fox matrix `J_{r,s} = ∂r/∂s` mapped to `k[K]`. For a word `r` of length
`<= L`, every term of `∂r/∂s` is `±` the image of a proper prefix of `r`, so every entry of `J`
is supported in `B_{L−1} ⊂ B_L`.

For `H <= K` of finite index, `X_H = H\X̃` is a `K(H, 1)`. Its chains are
`k[H\K] ⊗_{k[K]} C_*(X̃)`, where `k[H\K]` is the permutation module of the right `K`-set `H\K`.
The map `π : k[K] → k[H\K]`, `g ↦ Hg`, is a map of right `k[K]`-modules. Coordinatewise it gives
maps `π : C_q(X̃) → C_q(X_H)` of chain complexes. In particular, `π(aJ) = π(a)J`.

The cover `Y_L^{(H)} = H\Ỹ_L ⊂ X_H` has no 3-cells, so

> `H_2(Y_L^{(H)}; k) = Z := ker(J_H : k[H\K]^c → k[H\K]^n)`, with `J_H(u) = uJ`.

Let `Γ_L`, `H_L` and `M_L` be as in the target. Then `Y_L^{(H)}` is the cover of `Y_L` for the
subgroup `H_L <= Γ_L = π_1(Y_L)`, so by Hopf the map `H_2(Y_L^{(H)}) → H_2(H_L)` is onto. The
inclusion `Y_L^{(H)} ⊂ X_H` induces `H_2(H_L) → H_2(H)` on group homology. Hence

> `I_L(H) = image of Z in H_2(X_H; k) = Z / (Z ∩ B_2(X_H))`, where `B_2 = ∂_3 C_3(X_H)`.

## 2. Proof of item 1

Let `T` be a transversal of `H`. Put `k[T]^c = {a ∈ k[K]^c : supp a_r ⊂ T for all r}`.

*Step 1: cycles on `T` die.* Let `W_T = {a ∈ k[T]^c : aJ = 0}`. Every `a ∈ W_T` is a 2-cycle of
`X̃` with coefficients in `k`. Since `X̃` is contractible, `H_2(X̃; k) = 0`, so `a = ∂_3 b` for
some `b ∈ C_3(X̃)`. Then `π(a) = ∂_3 π(b) ∈ B_2(X_H)`, and `π(a) ∈ Z` because `π(a)J = π(aJ) = 0`.
So `π(W_T) ⊂ Z ∩ B_2(X_H)`. Since `T` is a transversal, `π` restricted to `k[T]` is an
isomorphism onto `k[H\K]`, so `dim π(W_T) = dim W_T`.

*Step 2: rank-nullity on `T`.* Let `V = k[T]^c J ⊂ k[K]^n`. Rank-nullity for `a ↦ aJ` on
`k[T]^c` gives `dim W_T = c|T| − dim V`. Every `a ∈ k[T]^c` has `aJ` supported in `T B_L`,
because `(t e_r) J = t · J_r` and `J_r` is supported in `B_L`. So `V ⊂ k[T B_L]^n`.

*Step 3: the quotient only loses the boundary.* Since `π(k[T]^c) = k[H\K]^c`, the image of `J_H`
is `π(V)`, so `dim Z = c[K:H] − dim π(V)`. The restriction
`π : k[T B_L]^n → k[H\K]^n` is onto, because `1 ∈ B_L` means `T ⊂ T B_L`. Its kernel therefore has
dimension `n(|T B_L| − [K:H]) = n |T B_L \ T|`, and so `dim π(V) >= dim V − n|T B_L \ T|`.

*Conclusion.* Using `|T| = [K:H]`,

> `dim I_L(H) <= dim Z − dim π(W_T) = (c[K:H] − dim π(V)) − (c|T| − dim V) = dim V − dim π(V)
> <= n |T B_L \ T|`.

*The injective variant.* Suppose `T` only injects into `H\K`. Steps 1 and 2 are unchanged.
In Step 3, `π(T B_L)` still contains the `|T|` points `π(T)`. So the kernel of `π` on
`k[T B_L]^n` has dimension at most `n|T B_L \ T|`, and the rank of `J_H` is at least
`dim π(V) >= dim V − n|T B_L \ T|`. Hence
`dim I_L(H) <= c[K:H] − dim V + n|T B_L \ T| − (c|T| − dim V) = n|T B_L \ T| + c([K:H] − |T|)`. ∎

**Remarks.** Nothing about `K` is used except that `X̃` is `k`-acyclic in degree 2. Normality
of `H` is not needed. The field `k` is arbitrary, so the bound holds for mod-`p` Betti numbers
too. The finite-quotient Swan theorem and the relation module play no role here. The relation
module enters only through item 4 of the base node, which identifies `lim b_2(N_i)/[K:N_i]`.

## 3. Proof of item 2

Let `N <= K` have finite index, and let `N_L` be its preimage in `Γ_L`. Since
`M_L = ker(Γ_L → K) <= N_L`, there is an extension `1 → M_L → N_L → N → 1`. Its five-term exact
sequence with coefficients in `k` is

> `H_2(N_L) → H_2(N) → H_0(N_L; H_1(M_L)) → H_1(N_L) → H_1(N) → 0`.

The image of the first map is `I_L(N)`. So `b_2(N) − dim I_L(N)` equals the dimension of the
kernel of the third map. By exactness at `H_1(N_L)`, the image of the third map is
`ker(H_1(N_L) → H_1(N))`, of dimension `b_1(N_L) − b_1(N)`. ∎

## 4. Proof of item 3

By Weiss's theorem, the nested residual chain `(N_i)` has fundamental domains `T_i` forming a
Følner sequence. For normal `N_i`, left and right cosets agree. If the `T_i` are left Følner,
then `T_i^{-1}` are right Følner transversals, since `t N_i ↦ t^{-1} N_i` is a bijection of
`K/N_i`. So for fixed `L`, `|T_i B_L \ T_i| = o(|T_i|) = o([K:N_i])`, and item 1 gives
`dim I_L(N_i) = o([K:N_i])`. ∎

## 5. Proof of item 4

Write `F_i = K/N_i`. Two facts about `K` come from item 4 of
`rf-weak-bass-defect-is-degree-two-approximation-defect`:

- (F1) `b_2(N_i) / |F_i| → χ_Q(K)`;
- (F2) `χ_Q(K) = D(P) >= 0`.

Also, `χ_Q(K) = 1 − b_1(K) + b_2(K)` is an integer, and by item 3 of that node every `b_2(N_i)`
is finite, so `ℓ^δ(N_i)` is defined.

*(a) ⇒ (b).* Fix `δ > 0`. For large `i`, `b_2(N_i) <= δ|F_i|`. Then `L = 0` satisfies
`dim I_0(N_i) >= 0 >= b_2(N_i) − δ|F_i|`, so `ℓ^δ(N_i) = 0`. And `ρ_δ(N_i) >= 0`, because
`T B_0 \ T = ∅` for every transversal.

*(b) ⇒ (c).* Take `δ = ε` with `δ(1 + n) < 1`.

*(c) ⇒ (a).* Let `i` be one of the infinitely many indices, `L = ℓ^δ(N_i)`, and `T` a
transversal with `|T B_{L'} \ T| <= ε|T|` for some `L' >= L`. Such `L'` exists because
`L <= ρ_ε(N_i)`: if the sup is attained, use it; otherwise take any admissible `L' >= L`. Balls
increase, so `|T B_L \ T| <= ε|T|`. By item 1,

> `b_2(N_i) <= dim I_L(N_i) + δ|F_i| <= n ε |F_i| + δ|F_i|`.

So `liminf_i b_2(N_i)/|F_i| <= δ + nε < 1`. By (F1) the limit exists and equals the integer
`χ_Q(K)`, so `χ_Q(K) <= 0`. By (F2), `χ_Q(K) = 0`, and then (F1) gives (a). ∎

## 6. Proof of item 5

Suppose `χ_Q(K) >= 1`. If `ℓ^δ(N_i) <= ρ_ε(N_i)` held for infinitely many `i` with
`δ + nε < 1`, then (c) would hold, and so would (a), which is a contradiction. So the inequality
fails for all large `i`. Weiss's Følner transversals give `ρ_ε(N_i) → ∞` for every `ε > 0`, and
hence `ℓ^δ(N_i) → ∞`. The last formula combines item 3 with (F1):
`b_2(N_i) − dim I_L(N_i) = χ_Q(K)|F_i| + o(|F_i|) − o(|F_i|)`. ∎

## 7. Proof of item 6 (calibration)

Take `Γ` and its presentation from `pro-p-route-cannot-see-amenability-in-cd-two`. The quotient
`Γ\Δ` of the building is a finite aspherical 2-complex with `V` vertices, `7V` edges and `7V`
triangles. Collapsing a maximal tree (`V − 1` edges) gives an aspherical presentation with
`n = 6V + 1` generators and `7V` relators, each of length `<= 3`. These relators normally generate
`R`, so `Γ_3 = Γ`, hence `N_3 = N` and `I_3(N) = H_2(N; Q)`. Property (T) gives
`b_1(N; Q) = 0`, and multiplicativity of `χ` for type-F groups gives
`b_2(N; Q) = V[Γ:N] − 1`. Item 1 is then the displayed inequality.

That inequality is consistent: `Γ` is non-amenable, so there is `h > 0` with
`|T B_1 \ T| >= h|T|` for every finite `T ⊂ Γ` (Følner's criterion). The proof of item 1 used
nothing about the group except asphericity of the universal cover, and asphericity holds for
`Γ`. So Steps 1–3 hold verbatim for `Γ`. The only step of the scheme that cannot be carried out for
`Γ` is choosing `T` with `|T B_3 \ T| = o(|T|)`, which needs amenability.

Conversely, suppose `K` is amenable but not finitely presented. That step can be carried out
for each fixed `L` (item 3), and the scheme fails instead because `L` must grow (item 5). So the
two ways the scheme can fail are separated:

| group | small-boundary transversals | bounded relator depth | `lim b_2(N_i)/index` |
|---|---|---|---|
| Kazhdan lattice `Γ` | fail (non-amenable) | hold (`L = 3`) | `V = b_2^{(2)}(Γ)` |
| f.p. amenable (e.g. `BS(1,m)`, `Z²`) | hold | hold | `0` |
| amenable cd-2 counterexample | hold for each fixed `L` | fail (`ℓ^δ → ∞` faster than `ρ_ε`) | `χ_Q(K) >= 1` |

## 8. What would close the residually finite case

By item 4, it suffices to find a residual chain and `δ + nε < 1` such that
`ℓ^δ(N_i) <= ρ_ε(N_i)` infinitely often. By item 2, this means the long relations have small
coinvariants: for `L = ρ_ε(N_i)`,

> `dim H_0(N_{i,L}; H_1(M_L; Q)) − b_1(N_{i,L}) + b_1(N_i) <= δ [K:N_i]`.

Here `b_1(N_i) = O(√[K:N_i])` for a counterexample (`amenable-cd-two-pro-p-completions-not-golod-shafarevich`,
item 2), so the question is about `H_0(N_{i,L}; H_1(M_L; Q))` against `b_1(N_{i,L})`. It is a
statement about the finitely presented groups `Γ_L`, which are typically non-amenable, and their
finite quotients `K/N_i`: the long relations `M_L` must become almost trivial in the
`N_{i,L}`-coinvariants once `L` reaches the Følner radius of `K/N_i`.
