---
rg: 2
id: rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp-proof
kind: route
title: Translations have trivial word sections, and lamp conjugates at distance k split into constant sections once nearer lamps commute, so the recursion of F/K_infty forces the lamplighter relations
target: rn-groups-of-affine-lamplighters-f-q-wr-z-are-fp
requires:
  - rover-nekrashevych-fp-iff-finite-lift-presentation
---

Notation and conventions are those of the claim and of `rover-nekrashevych-fp-iff-finite-lift-presentation`:
`g(xw) = g(x) g|_x(w)`, `(gh)|_x = g|_{h(x)} h|_x`, and `σ (g_x)_x` denotes the element with root permutation `σ`
and sections `g_x`. In a wreath product, `σ(g_x)_x · ρ(h_x)_x = σρ (g_{ρ(x)} h_x)_x`.

## 0. The automaton and the group

**Recursion.** Since `t = a + π`,

`t(x_0 + π y) + c = a x_0 + c + π(x_0 + t y)`.

So `B_c = β_c (B_x)_{x in F_q}` with `β_c(x) = a x + c`. Put `S = {B_c^{±1}}`. By
`(g^{-1})|_y = (g|_{g^{-1}(y)})^{-1}`, the set `S` is closed under sections, so `𝒜(q, a)` is finite-state.

**The group.** Write `τ_c = B_c B_0^{-1}` (the map `x ↦ x + c`) and `A = B_0` (the map `x ↦ t x`). Then `B_c = τ_c A`
freely, and `G = ⟨A, τ_c⟩ = {x ↦ t^n x + f : n in Z, f in F_q[t, t^{-1}]}`, because `A^k τ_c A^{-k}` is
`x ↦ x + t^k c`. Here `t = a + π` is a unit of `O`, so `F_q[t, t^{-1}] ⊆ O`.

**Faithfulness.** `F_q[t] -> F_q[[π]]`, `t ↦ a + π`, is injective (it is the substitution `F_q[t] ≅ F_q[π]`). Its
extension to `F_q[t, t^{-1}]` is injective as well, since `t` is a unit. Also `t^n ≠ 1` in `O` for `n ≠ 0`, since
`(a + π)^n` is a polynomial of degree `|n|` in `π` (use `t^{-1}` for `n < 0`). An affine map `x ↦ u x + f` of `O` is the
identity iff `f = 0` (evaluate at `0`) and `u = 1` (evaluate at `1`). So
`F_q[t^{±1}] ⋊ t^Z -> Homeo(O)` is injective, and
`G ≅ F_q[t^{±1}] ⋊ t^Z ≅ F_q ≀ Z` (lamp group `(F_q, +)`, with `t` acting as the shift).

Under this isomorphism, the standard generators of `F_q ≀ Z` (lamp `c` at `0`, and the shift) go to `τ_c` and `A`.

**Not contracting, not finitely presented.** `A(0) = 0` and `A|_0 = B_0 = A`, so `A^m|_{0^n} = A^m` for all `m, n`.
The nucleus would have to contain every `A^m`, and these are distinct. `F_q ≀ Z` is not finitely presented
(Baumslag, 1961).

## 1. The recursion of `Ĝ = F/K_∞`

By (1b) and (1d) of the Theorem A route with `R = ∅`, `K_∞` is a section-closed lift ideal and
`ψ̂: Ĝ -> Ĝ ≀ Sym(F_q)` is injective. Everything below is computed in `Ĝ`, and every step is either a free
computation of word-level sections or an application of injectivity of `ψ̂`.

**(1a) Translations.** The root permutation of `B_0^{-1}` is `y ↦ y/a`, and `B_0^{-1}|_y = (B_{y/a})^{-1}`. Hence

`τ_c|_y = B_c|_{y/a} · B_0^{-1}|_y = B_{y/a} B_{y/a}^{-1}`,

which is freely trivial, and `τ_c(y) = y + c`. So at the word level `ψ(τ_c) = (+c)(1, ..., 1)`.

- Any word `W` in the `τ_c^{±1}` then has freely trivial sections, and root permutation `+Σ(±c_i)`.
- If that sum is `0`, then `W in K_1 ⊆ K_∞`.
- So in `Ĝ` the map `c ↦ τ_c` is a homomorphism `(F_q, +) -> Ĝ`. It is injective, since root permutations separate
  its values. Write `T = {τ_c} ≅ (F_q, +)`.

**(1b) The shift.** `ψ̂(A) = α (τ_x A)_{x in F_q}`, where `α(x) = a x`. Iterating with `(gh)|_x = g|_{h(x)} h|_x`:

`A^k|_y = A|_{a^{k-1} y} ··· A|_{a y} A|_y = τ_{a^{k-1} y} A τ_{a^{k-2} y} A ··· τ_y A`  (`k ≥ 1`).

Write `d_j(c) = A^j τ_c A^{-j}` for `j in Z` and `c in F_q`. Moving each `A` to the right gives

`A^k|_y = D_k(y) A^k`, where `D_k(y) = d_0(a^{k-1} y) d_1(a^{k-2} y) ··· d_{k-1}(y)`.

Each `c ↦ d_j(c)` is a homomorphism `(F_q, +) -> Ĝ`, being a conjugate of `c ↦ τ_c`.

**(1c) Sections of a lamp at distance `k ≥ 1`.** The root permutation of `d_k(c)` is `x ↦ x + a^k c`. Its section at
`x` is computed with `y = A^{-k}(x) = a^{-k} x` and `(A^{-k})|_x = (A^k|_y)^{-1}`, and `τ_c` has trivial sections:

`d_k(c)|_x = A^k|_{y + c} · τ_c|_y · (A^k|_y)^{-1} = D_k(y + c) A^k A^{-k} D_k(y)^{-1} = D_k(y + c) D_k(y)^{-1}`.

## 2. All lamps commute in `Ĝ`

Let `P(k)` say that `[d_i(c), d_j(c')] = 1` in `Ĝ` for all `c, c' in F_q` and all `i, j` with `|i - j| ≤ k`.

- `P(0)` holds: `d_i(c)` and `d_i(c')` are conjugates of the commuting `τ_c, τ_{c'}` by the same element (1a).
- **Step.** Assume `P(k-1)` with `k ≥ 1`. Then `d_0(·), ..., d_{k-1}(·)` pairwise commute, and each is additive in
  its argument. So

  `D_k(y + c) D_k(y)^{-1} = ∏_{j<k} d_j(a^{k-1-j}(y + c)) d_j(a^{k-1-j} y)^{-1} = ∏_{j<k} d_j(a^{k-1-j} c) = D_k(c)`,

  independently of `x`. By (1c), `ψ̂(d_k(c)) = (+a^k c)(M, ..., M)` with `M = D_k(c)`.
- Also `ψ̂(τ_{c'}) = (+c')(1, ..., 1)`. With the product rule for elements with constant sections:

  `ψ̂(τ_{c'} d_k(c)) = (+c' + a^k c)(M, ..., M) = ψ̂(d_k(c) τ_{c'})`.

  Since `ψ̂` is injective, `[τ_{c'}, d_k(c)] = 1` in `Ĝ`. Conjugating by `A^i` gives `[d_i(c'), d_{i+k}(c)] = 1` for
  all `i`. The case `j = i - k` follows by inverting the commutator. Together with `P(k-1)`, this gives `P(k)`. ∎

## 3. `N = K_∞`

Let `L = F_q ≀ Z = ⟨T_0, s | [c, s^k c' s^{-k}] = 1 for k ≥ 1⟩`, where `T_0 ≅ (F_q, +)`. This is the standard
presentation of `B ≀ Z`: the relations make the conjugates `s^k T_0 s^{-k}` pairwise commute, so they generate
`⊕_Z T_0`, normalized by `s`.

- By (1a) and §2 there is a homomorphism `λ: L -> Ĝ` with `c ↦ τ_c` and `s ↦ A`. It is surjective, since
  `B_c = τ_c A`.
- The composite `L -> Ĝ -> G` sends `c` to `x ↦ x + c` and `s` to `x ↦ t x`. By §0 this is the isomorphism
  `F_q ≀ Z ≅ G`.
- So `λ` is injective, hence bijective, and `Ĝ -> G` is an isomorphism. That is, `N = K_∞`.

No Hopficity is used. By Theorem A (consequence 2), `V_q(G)` is finitely presented by the Higman–Thompson relations,
(C) and (S). This proves (1) and (2) of the claim. ∎

## 4. The extension `G^+ = AGL_1(F_q[t, t^{-1}])`

Add the states `μ_u` for `u in F_q^× \ {1}`, with `μ_u(x) = u x`, and read `μ_1` as the empty word. Since
`u(x_0 + π y) = u x_0 + π u y`, we get `μ_u = (x ↦ u x)(μ_u, ..., μ_u)`. So `S^+ = S ∪ {μ_u^{±1}}` is closed under
sections. Let `F^+ = F(S^+)` and `N^+ = ker(F^+ -> G^+)`.

**(4a) `G^+ ≅ G ⋊ F_q^×`.** `μ_u B_c μ_u^{-1}` is `x ↦ u(t u^{-1} x + c) = t x + uc`, which is `B_{uc}`. So `F_q^×`
acts on `G` by the automorphism `φ_u` fixing `A` and sending `τ_c ↦ τ_{uc}`. The group
`G^+ = F_q[t^{±1}] ⋊ (t^Z × F_q^×)` is the full affine group of `O_{\{0,∞\}} = F_q[t^{±1}]`, whose unit group is
`F_q^× × t^Z`. Faithfulness is as in §0, since `u t^n = 1` in `O` only if `n = 0` and `u = 1`.

**(4b) `R_μ` is section-closed.** For `ρ = μ_u μ_{u'} μ_{uu'}^{-1}`, every word-level section is `ρ` itself. For
`κ_{u,c} = μ_u B_c μ_u^{-1} B_{uc}^{-1}`, the section at `x` is computed with `z = B_{uc}^{-1}(x) = (x - uc)/a`:

`κ_{u,c}|_x = μ_u · B_c|_{z/u} · μ_u^{-1} · (B_{uc}|_z)^{-1} = μ_u B_{z/u} μ_u^{-1} B_z^{-1} = κ_{u, z/u}`.

So `R_μ` is closed under word-level sections, and `R_μ ⊆ N^+` by (4a).

**(4c) `N^+ = ⟨⟨R_μ⟩⟩_lift`.** Let `M = ⟨⟨R_μ⟩⟩_lift ⊆ N^+`. By (1b) of the Theorem A route, `M` is section-closed.
By (1d), `Q = F^+/M` has injective recursion (not needed below). Let `H ≤ Q` be the image of `F = F(S)`.

- `K_∞(F) ⊆ K_∞(F^+) ⊆ M`, because a word over `S` that dies after free splittings in `𝒜(q, a)` dies in the larger
  automaton too. So `F -> H` factors through `F/K_∞(F) = G` (§3), giving a surjection `G -> H`.
- The image `U` of the `μ_u` is a quotient of `F_q^×`, by the relators `ρ`.
- By the relators `κ`, `U` normalizes `H`, and conjugation by `μ_u` acts on `H` through `φ_u`.
- So `G ⋊ F_q^× -> Q` is well defined and surjective. The composite `G ⋊ F_q^× -> Q -> G^+` is the isomorphism
  (4a). Hence `Q -> G^+` is injective, that is `M = N^+`.

By Theorem A, `V_q(G^+)` is finitely presented, with the extra finite relator set `L(R_μ)`.

**(4d) `N^+ ≠ K_∞`.** A word in the `μ_u^{±1}` alone is its own section at every letter. Every section of `κ_{u,c}`
with `u ≠ 1` is again some `κ_{u,c'}`, which is freely reduced and nontrivial. So no freely nontrivial element of
`R_μ` becomes freely trivial after splitting, and none lies in `K_∞`. `afflamp.py --mu` confirms this for
`p = 3, 5`.

**(4e) Finiteness length.** `AGL_1(O_S)` with `|S| = 2` is of type `F_1` but not `FP_2` (Bux 1997; SWZ Theorem 6.8).
So `V_q(G^+)` is `F_2` while `G^+` is not. The SWZ persistent extension of this action to `T_{q+1}` (their Lemma 5.3)
has `V_{q+1}(G^+)` not finitely presented, by `persistent-automata-rn-group-fp-iff-group-fp` (or SWZ Theorem 5.8).
So SWZ's Theorem 5.8 fails without its persistence hypothesis, even within the coarsely diagonal affine family it is
applied to. This proves (3) and (4) of the claim. ∎

## 5. Machine check

`experiments/affine-lamplighter-rn-2026-09-17/afflamp.py p a K [--mu] [--persist]` (prime `p` only) builds
`𝒜(p, a)` with the `Automaton` class of `experiments/nonc-rn-fp-2026-09-17/autom.py`. It tests each relator for
membership in `N` and in `K_∞`, using the finite reachable-section graph of Theorem A, consequence 4. The relators
tested are `τ_c = τ^c`, `τ^p` and `[τ, A^k τ A^{-k}]` for `k ≤ K`. Results in `results.txt`:

- `(p, a, K) = (2,1,6), (3,1,5), (3,2,5), (5,1,4), (5,2,4), (7,3,4)`: all relators in `K_∞`. This agrees with §2,
  and is an independent check of the induction.
- `--mu` with `(3,1)`, `(5,2)`: the lamplighter relators are in `K_∞`, and the `μ` relators are in `N \ K_∞`,
  as (4d) says.
- `--persist`: all relators in `N \ K_∞`, as `persistent-automata-rn-group-fp-iff-group-fp` predicts.

The proof in §§1–4 covers all prime powers `q`. The script handles prime fields only.
