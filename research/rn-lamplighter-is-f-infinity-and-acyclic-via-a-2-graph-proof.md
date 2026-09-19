---
rg: 2
id: rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph-proof
kind: route
title: The balls of O with an ancestor of the simply transitive level-1 vertex form a one-vertex 2-graph monoid in Aff(R) whose path groupoid is the germ groupoid of V_2(Z/2 wr Z); Li's k-graph theorem gives F_infinity and a Koszul complex with 1 - 2 = -1 gives acyclicity
target: rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph
requires:
  - rn-lamplighter-is-a-function-field-stein-group
  - li-finite-k-graph-full-groups-are-f-infinity
  - finite-k-graph-boundary-groupoid-standard-facts
  - li-derived-full-group-homology-is-k-theory-cover
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/two_graph.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-two-graph.txt
---

## Notation

- `K = F_2(t)` and `π = 1 + t`. For a place `v`, `|·|_v` is the normalised absolute value, with `|t|_0 = 1/2`,
  `|t|_∞ = 2` and `|π|_π = 1/2`.
- `O = F_2[[π]] ⊂ K_π`, and `R = F_2[t, 1/t, 1/π]`, with `R^× = t^Z × π^Z`.
- By Lemma 1.1 of `rn-lamplighter-is-a-function-field-stein-group-proof`, `R ∩ O = F_2[t^{±1}]`.
- `a = (u, b)` denotes `x ↦ ux + b`.
- `T_v` is the Bruhat–Tits tree of `K_v`, and its vertices are balls. `Aff(K_v)` acts on balls. "`B'` is an ancestor
  of `B`" means `B' ⊇ B`.
- In `X = T_0 × T_∞`, the ancestor quadrant of a vertex `(B_0, B_∞)` is the set of pairs `(B'_0, B'_∞)` with
  `B'_0 ⊇ B_0` and `B'_∞ ⊇ B_∞`.
- `ρ_* = (F_2[[t]], t^{-1}F_2[[t^{-1}]])`, and `A(ρ_*)` is its ancestor quadrant.
- For `m, n ≥ 0`, `anc_{m,n}(ρ_*) = (t^{-m}F_2[[t]], {|x|_∞ ≤ 2^{n-1}})` is the unique ancestor that is `m` steps up
  in `T_0` and `n` steps up in `T_∞`.

## 1. The monoid `P` and its degree

**Lemma 1 (description of `P`).** Let `a = (t^i π^j, b) ∈ Aff(R)`, and put `m = -i`, `n = i + j`. Then `a ∈ P`
exactly when all of the following hold:
- `m ≥ 0` and `n ≥ 0`;
- `b ∈ F_2[t^{±1}]`;
- `ord_0 b ≥ -m` and `deg b ≤ n - 1`.

In that case `a(ρ_*) = anc_{m,n}(ρ_*)` and `a(O) = b + π^{m+n}O`.

*Proof.* The condition `a(O) ⊆ O` means two things:
- `a(O) = b + π^j O`, since `|t|_π = 1`;
- so `j ≥ 0`, and `b ∈ O ∩ R = F_2[t^{±1}]`.

In `T_0`, `a(F_2[[t]]) = b + t^{-m}F_2[[t]]`, because `π` is a unit at `0`. This ball contains `F_2[[t]]` exactly
when `m ≥ 0` and `ord_0 b ≥ -m`.

In `T_∞`, `|t^i π^j|_∞ = 2^{i+j} = 2^n`. So `a(t^{-1}F_2[[t^{-1}]]) = b + {|x|_∞ ≤ 2^{n-1}}`. This contains
`t^{-1}F_2[[t^{-1}]]` exactly when `n ≥ 0` and `deg b ≤ n - 1`.

Finally `j = m + n`. ∎

**Consequences.**
- `P` is a monoid: `ρ_* ∈ A(ρ_*)`, and `a(A(ρ_*)) ⊆ A(a ρ_*)`. So `a, a' ∈ P` gives
  `aa'ρ_* ∈ a(A(ρ_*)) ⊆ A(ρ_*)`, and `aa'(O) ⊆ O`.
- `d(a) = (-i, i+j) = (log_2|u|_0, log_2|u|_∞)` is a homomorphism on all of `Aff(R)`.
- **Trivial units.** `d^{-1}(0,0) ∩ P = {id}`. Indeed `m = n = 0` forces `b ∈ span(∅) = 0`. This is the simple
  transitivity of `G` on level `1`, in the form "`a ρ_* = ρ_*` and `a(O) = O` forces `a = 1`".
- By Lemma 1, `P_{(m,n)} = {(t^{-m}π^{m+n}, b) : b ∈ span(t^{-m}, ..., t^{n-1})}`, which has `2^{m+n}` elements.
- The map `b ↦ b mod π^{m+n}` from `span(t^{-m}, ..., t^{n-1}) = t^{-m}·F_2[t]_{<m+n}` to `F_2[t]/(π^{m+n})` is
  bijective. Polynomials of degree `< N` represent `F_2[t]/(π^N)` uniquely, and `t` is a unit mod `π`. So `a ↦ a(O)`
  is a bijection from `P_{(m,n)}` onto the balls of depth `m + n` in `O`.

**Lemma 2 (unique factorisation).** Let `a ∈ P` with `d(a) = p + q` and `p, q ∈ N²`. Then there are unique
`a' ∈ P_p` and `a'' ∈ P_q` with `a = a'a''`.

*Proof.* **Uniqueness.** `a'` determines `a'' = a'^{-1}a`. Also `a'(O) ⊇ a(O)` is a ball of depth `|p|`, and there
is exactly one such ball. By the bijection above, `a'` is unique.

**Existence.** Write `a = (t^{-m}π^{m+n}, b)` and `p = (m', n')`. Let `a' = (t^{-m'}π^{m'+n'}, b')` be the element
with `a'(O) ⊇ a(O)`, that is, `b ≡ b' mod π^{m'+n'}`. Then
`a'' = a'^{-1}a = (t^{-(m-m')}π^{(m-m')+(n-n')}, b'')` with `b'' = t^{m'}π^{-(m'+n')}(b - b')`. We check Lemma 1 for
`a''`:
- `b''` is a Laurent polynomial, since `π^{m'+n'}` divides `b - b'` in `F_2[t^{±1}]`.
- `ord_0 b'' ≥ m' - m`, since `ord_0(b - b') ≥ -m`.
- `deg b'' = m' - (m'+n') + deg(b - b') ≤ n - n' - 1`.

So `a'' ∈ P_q`. ∎

The degree-`(1,0)` elements are `e_c = (π/t, c/t)` and the degree-`(0,1)` elements are `f_c = (π, c)`, for
`c ∈ {0, 1}`. Now `e_i f_j(x) = (π²/t)x + (πj + i)/t` and `f_{i'} e_{j'}(x) = (π²/t)x + (πj' + i't)/t`. Since
`t = π + 1`, these agree exactly when `i' = i` and `j' = i + j`. So `e_i f_j = f_i e_{i+j}`. By Lemma 2 these four
relations are all of them, and `(P, d)` is the one-vertex 2-graph `Λ` with this factorisation bijection. It is
finite, and has `#d^{-1}(ε_1) = #d^{-1}(ε_2) = 2`.

Also `λ_c = f_c`, while `e_0 = λ_0 ∘ (x ↦ t^{-1}x)` and `e_1 = λ_1 ∘ (x ↦ t^{-1}x + t^{-1})`. The check is
`1 + π(x+1)/t = (πx + 1)/t`, using `t + π = 1`.

## 2. The groupoids agree

**Path space.** `Λ` is row-finite and has no sources. An infinite path is a compatible family
`x(0, (m,m)) ∈ P_{(m,m)}`, `m ≥ 0`. Under `a ↦ a(O)` these become nested balls of depth `2m`. So
`Λ^∞ → O`, `x ↦ ∩_m x(0,(m,m))(O)`, is a homeomorphism, and it carries the left action of `p ∈ P` on paths to the
map `p: O → p(O)`.

**Germs.** By `finite-k-graph-boundary-groupoid-standard-facts` (item 1), `G_Λ` is Li's `I_l ⋉ ∂Ω`, with basis
`Z(μ, ν) = {(μz, d(μ) - d(ν), νz)}`. Under `Λ^∞ ≅ O`, the bisection `Z(μ, ν)` is the graph of the affine map
`μν^{-1}: ν(O) → μ(O)`. So there is a continuous groupoid map `Φ: G_Λ → 𝒢`, `(μz, d(μ)-d(ν), νz) ↦ germ of μν^{-1}`.

- **Well defined and injective.** The lag `d(μ) - d(ν) = d(μν^{-1})` depends only on the affine map, and `d` is a
  homomorphism. Two distinct affine maps agree at no more than one point. So a germ of an element of `Aff(R)` at
  a non-isolated point determines the element, and hence the lag.
- **Effective.** In particular `G_Λ` is effective: an arrow acting trivially near its source has `μν^{-1} = 1`.
- **Surjective.** Let `g ∈ Aff(R)` and `x ∈ O` with `g(x) ∈ O`. For `M ≥ 0` let `μ_M ∈ P_{(M,M)}` be the element
  with `x ∈ μ_M(O)`. Then `ν = gμ_M` lies in `P` for `M` large. Indeed:
  - `ν(O) = g(μ_M(O))` is a ball around `g(x)` of radius tending to `0`, so it lies in `O`;
  - `νρ_* = g(anc_{M,M}(ρ_*))` does not depend on the choice of `μ_M`. Its `T_0`-component is
    `b_g + u_g t^{-M}F_2[[t]]` and its `T_∞`-component is `b_g + {|x|_∞ ≤ |u_g|_∞ 2^{M-1}}`. For large `M` both
    contain `ρ_*`'s components, whatever `b_g ∈ R` is.

  Hence the germ of `g` at `x` is `Φ(ν z, d(ν) - d(μ_M), μ_M z)`. ∎

So `Φ` is an isomorphism of ample groupoids, and `F(G_Λ) = F(𝒢) = PAff(O; R) = V_2(G)` by
`rn-lamplighter-is-a-function-field-stein-group` (1).

`experiments/rn-lamplighter-finiteness-2026-09-17/two_graph.py` checks the following exactly, in Laurent-polynomial
arithmetic:
- the four relations;
- `|P_{(m,n)}| = 2^{m+n}` and the ball bijection, for `m, n ≤ 4`;
- that every word in `e_*` and `f_*` of degree `(m,n)` lies in `P_{(m,n)}`, and that each ordering of colours hits
  every element exactly once;
- that factorisation is unique, over 300 random cases with `m, n ≤ 6`;
- the germ step: for 33 random `g ∈ Aff(R)` with `π`-poles, every sampled admissible `μ ∈ P_{(M,M)}` gives
  `gμ ∈ P` once `M ≥ 11`.

Output: `results-two-graph.txt`, `ALL OK`.

## 3. Type `F_∞`

`Λ` is a finite one-vertex 2-graph with two loops of each colour. By `li-finite-k-graph-full-groups-are-f-infinity`
(Li, arXiv:2110.04505, Corollary 7.4), applied with `X = ∂Ω` and `Y = X(1; ∅) = ∂Ω`, `F(G_Λ)` is of type `F_∞`. So
`V_2(Z/2 ≀ Z)` is of type `F_∞`. ∎

## 4. `H_*(𝒢; Z) = 0`

**First computation.** `O` is a clopen subset of `K_π` that meets every orbit. So `𝒢 = (Aff(R) ⋉ K_π)|_O` is Morita
equivalent to `Aff(R) ⋉ K_π`, and for every coefficient group `A`,
`H_*(𝒢; A) = H_*(Aff(R); C_c(K_π, A))`.

*Step 1: the translation subgroup `R`.*
- `C_c(K_π, A) = colim_k A[K_π/π^kO]`. The transition maps send `δ_C` to the sum of the indicators of the two
  subcosets of `C`.
- `R` is dense in `K_π`, so it acts transitively on `K_π/π^kO`, with stabiliser `R_k = R ∩ π^kO`. So
  `A[K_π/π^kO] = Ind_{R_k}^R A`.
- By Shapiro's lemma, and since homology commutes with colimits,
  `H_q(R; C_c(K_π, A)) = colim_k H_q(R_k; A)`, where the maps are the transfers for `R_{k+1} ⊂ R_k`, of index `2`.
- `R_k` is an `F_2`-vector space, and `R_{k+1}` is a direct summand of it.

*Step 2: `A = F_2`.*
- Let `pr: R_k → R_{k+1}` be a retraction. Then `res = pr^*` is onto in `F_2`-cohomology.
- For every class `b`, the projection formula gives `cor(b) = cor(res(pr^*b)·1) = pr^*b · cor(1) = 2·pr^*b = 0`.
- Dually the homology transfers vanish, including in degree `0`, where the transfer is multiplication by `2`.
- So `H_*(R; C_c(K_π, F_2)) = 0`, and by Lyndon–Hochschild–Serre over `R^×`, `H_*(𝒢; F_2) = 0`.

*Step 3: `A = Z[1/2]`.*
- `R_k` is a `2`-torsion group, so `H_q(R_k; Z[1/2]) = 0` for `q > 0`.
- In degree `0` the transfers are multiplication by `2`, which is invertible. So
  `H_*(R; C_c(K_π, Z[1/2])) = Z[1/2]`, concentrated in degree `0`, and identified through Haar measure.
- `t` acts on it trivially (`|t|_π = 1`), and `π` acts by `2^{-1}`.
- For the `π`-factor, `1 - 2^{-1}` is invertible on `Z[1/2]`, so `H_*(⟨π⟩; Z[1/2]) = 0`. By LHS,
  `H_*(𝒢; Z[1/2]) = 0`.

*Step 4: back to `Z`.* By the universal coefficient theorem:
- `H_n(𝒢; F_2) = 0` forces `H_n(𝒢; Z) ⊗ F_2 = 0` and `Tor(H_{n-1}(𝒢; Z), F_2) = 0`.
- `H_n(𝒢; Z[1/2]) = 0` makes `H_n(𝒢; Z)` a `2`-primary torsion group.
- A `2`-primary torsion group with no `2`-torsion is `0`.

So `H_n(𝒢; Z) = 0` for all `n ≥ 0`.

**Second computation.** For a row-finite `k`-graph with no sources, `H_*(G_Λ)` is the homology of the Koszul-type
complex `⊗_i (Z Λ^0 --(1 - M_i^t)--> Z Λ^0)` (Farsi–Kumjian–Pask–Sims, arXiv:1808.07807). For one vertex and
`M_1 = M_2 = (2)`, both maps are `-1`, so the complex is exact. This agrees with the first computation.

## 5. Acyclicity and simplicity

`𝒢` meets the hypotheses of Li's Corollary D (arXiv:2209.08087; setting as in
`li-derived-full-group-homology-is-k-theory-cover`):
- **Ample, Hausdorff, effective** (§2).
- **Unit space.** `O` is a Cantor set, with no isolated points.
- **Minimal.** The orbit of `x` contains every `λ_w(x)`, so it is dense.
- **Comparison.** There is no invariant probability measure: `μ(O) = μ(e_0 O) + μ(e_1 O) = 2μ(O)`. So comparison
  asks that every compact open `U` be moved by a bisection into every nonempty compact open `V`. That holds: `V`
  contains a ball `μ(O)` with `μ ∈ P`, and the bisection `μ` maps `O ⊇ U` into it.

Corollary D, with `H_*(𝒢) = 0` in all degrees, gives:
- `F(𝒢) = V_2(G)` is integrally acyclic;
- `F(𝒢) = D(𝒢)`, so `V_2(G)` is perfect.

`D(𝒢)` is simple for minimal effective ample groupoids on the Cantor set (Matui; Nekrashevych). Hence `V_2(G)` is
simple. This is consistent with (S) and (Ab) of `rover-nekrashevych-finite-presentation-criteria`.

## 6. General `q`

Take `π = t - a` with `a ∈ F_q^*`, `O = F_q[[π]]`, and `R = F_q[t, 1/t, 1/π]`. Replace `Aff(R)` by
`R ⋊ ⟨t, π⟩`, which is the multiplier group of `V_q(F_q ≀ Z)` (by `rn-lamplighter-is-a-function-field-stein-group`
(1)).
- Lemma 1 and Lemma 2 hold verbatim over `F_q`. `P_{(m,n)}` now has `q^{m+n}` elements, and level `1` is simply
  transitive, because `H^0` and `H^1` of `O(-1)` on `P^1` vanish.
- The edges are `e_c = (π/t, c/t)` and `f_c = (π, c)`, and `e_i f_j = f_{i/a} e_{j - i/a}`.
- §§2–3 are unchanged, so `V_q(F_q ≀ Z)` is of type `F_∞`.
- The Koszul complex on `(1-q, 1-q)` over `Z` gives `H_0 = Z/(q-1)`, `H_1 = Z/(q-1)` and `H_2 = 0`.
- By Li's Corollary C (rational) and Corollary E (the surjection `H_1(F) → H_1(𝒢)`), `V_q(F_q ≀ Z)` is rationally
  acyclic, and its abelianisation maps onto `Z/(q-1)`.

## 7. Not `2V`

In `𝒢`, the isotropy at `x ∈ O` is `Stab_{Aff(R)}(x)`, because germs determine the affine map.
- If `x ∉ K`, it is trivial: `ux + b = x` with `u ≠ 1` forces `x ∈ K`.
- If `x ∈ K`, it is `{u ∈ R^× : (1-u)x ∈ R}`, which is of finite index in `R^× ≅ Z²`. Write `x = r/s`. The group
  contains the kernel of `R^× → (F_2[t]/s')^×`, where `s'` is the part of `s` prime to `tπ`.

`2V` is the full group of `G_2 × G_2`, where `G_2` is the Cuntz groupoid on `{0,1}^N`. The isotropy at `(x, y)` is `Z`
when `x` is eventually periodic and `y` is not. Isotropy groups are invariants of the groupoid.

The spatial realisation theorem for topological full groups of minimal effective ample groupoids on the Cantor set
(Matui's isomorphism theorem, or Rubin's theorem) says an isomorphism `F(𝒢) ≅ F(G_2 × G_2)` would come from a
groupoid isomorphism. So `V_2(Z/2 ≀ Z) ≇ 2V`. This is at citation level only.
