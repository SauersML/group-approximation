---
rg: 2
id: block-permutation-transitions-force-divisible-classes-proof
kind: route
title: A block permutation is the line digraph of a regular multigraph, whose components carry k arcs per vertex; the constant permutation balances periodic classes, and far translates see independent sites
target: block-permutation-transitions-force-divisible-classes
requires: []
---

Complete proof. Notation as in the target. Conventions: `(h·x)(g) = x(h^(-1) g)`, and
`τ(x)(g) = μ(m ↦ x(gm))_{m ∈ M}`.

## Item 1. Divisibility

Let `E = ∪_b P_b × T_{f(b)} ⊆ R`. Build a multigraph `Γ` on the vertex set `I`. Each letter `x` is an arc from
`t(x)` to `f(b(x))`, where `x ∈ T_{t(x)}` and `x ∈ P_{b(x)}`.

- **Line digraph.** `(x, y) ∈ E` iff `y ∈ T_{f(b(x))}` iff `t(y) = f(b(x))`, i.e. the arc `y` starts where the arc `x`
  ends. So the digraph `(A, E)` is the line digraph `L(Γ)`.
- **Regular.** The out-degree of `c` in `Γ` is `|T_c| = k`. The in-degree of `c` is `|{x : f(b(x)) = c}| = |P_{f^(-1)(c)}| = k`.
- **Components are strongly connected.** In a digraph where every in-degree equals the out-degree, every weakly
  connected component is strongly connected: if some arc `u -> v` of a component had no path back, the set `X` of
  vertices reachable from `v` would contain `v` but not `u`. `X` is closed under outgoing arcs. So every arc leaving
  a vertex of `X` ends in `X`, hence `Σ_{w ∈ X} out(w)` arcs are inside `X`, while the arcs entering `X` number
  `Σ_{w ∈ X} in(w)`, which is the same sum. So every arc entering `X` starts in `X`, contradicting `u -> v`.
- **Arcs.** If `Γ_0` is a strongly connected component with at least one arc, `L(Γ_0)` is strongly connected: for
  arcs `x, y` of `Γ_0` take a path in `Γ_0` from the head of `x` to the tail of `y`; its arcs give a walk
  `x -> ... -> y` in `L(Γ)`. Every vertex of `Γ` has out-degree `k >= 1`, so every component has arcs, and every
  arc lies on a cycle of `L(Γ)`.
- **Count.** A component `Γ_0` with vertex set `V_0` has `k |V_0|` arcs, all starting in `V_0`. So the classes of `E`
  are the arc sets of the components, of sizes `k |V_0|`.
- **Passing to `R ⊇ E`.** Each class of `E` is strongly connected in `R`, and the classes of `R` partition `A`, so each
  class of `R` is a union of classes of `E`. Its size is a sum of multiples of `k`. Every letter lies on a cycle of
  `E ⊆ R`. `∎`

## Item 2. Far translates

`T_s` commutes with the action: `T_s(h·y)(g) = y(h^(-1) g s) = (h·T_s y)(g)`. It is a cellular automaton with memory
`{s}` and inverse `T_{s^(-1)}`. So `T_s ∘ τ` is injective iff `τ` is, and surjective iff `τ` is.

`(T_s ∘ τ)(x)(g) = τ(x)(gs) = μ(m ↦ x(gsm))`, which depends only on `x|_{gsM}`. If `s ∉ M^(-1)`, then `1 ∉ sM`, so
`g ∉ gsM`. Given letters `a, c`, choose `x` with `x(g) = a` and `x ≡ c` on `gsM`. Then
`(x(g), (T_s ∘ τ)(x)(g)) = (a, μ(c^M)) = (a, π(c))`. Here `τ(c^G) = π(c)^G` since `c^G` is `G`-fixed, and `π` is
injective because `τ` is, hence a permutation of the finite set `A`. So `R(T_s ∘ τ) ⊇ A × A`, and `A × A` is a
`|A|`-block permutation with one block. `M` is finite and `G` infinite, so such `s` exists.

For a letter permutation `λ` applied sitewise, `R(λ)` is the graph of `λ`, whose classes are the `λ`-orbits, and
`T_s ∘ λ` is far for every `s != 1`, with `R = A × A`. Composing with `T_s^(-1)` returns `λ`. `∎`

## Item 3. Closure

**Products.** For `τ` on `A` with memory `M` and `σ` on `B` with memory `N`, `(τ × σ)(x, y) = (τ x, σ y)` has
`R(τ × σ) = {((a, b), (a', b')) : (a, a') ∈ R(τ), (b, b') ∈ R(σ)}`. The inclusion `⊆` is clear. For `⊇`, take
`u ∈ A^M` with `u(1) = a`, `μ(u) = a'` and `v ∈ B^N` with `v(1) = b`, `ν(v) = b'`. Put `x(gm) = u(m)`, `y(gn) = v(n)`,
and extend arbitrarily. The two coordinates are independent. If `E = ∪ P_b × T_{f(b)}` and
`E' = ∪ P'_{b'} × T'_{f'(b')}`, then `E ⊗ E' = ∪ (P_b × P'_{b'}) × (T_{f(b)} × T'_{f'(b')})` is a `k k'`-block
permutation of `A × B`, contained in `R(τ × σ)`. `τ × σ` is injective iff both are, and surjective iff both are.

**Letter permutations.** `R(λ ∘ τ ∘ λ') = {(λ'^(-1)(a), λ(a')) : (a, a') ∈ R(τ)}`, because
`(y(g), λ(τ(λ' y))(g))` with `x = λ' y` is `(λ'^(-1)(x(g)), λ(τ(x)(g)))`. The image of `E` is
`∪ λ'^(-1)(P_b) × λ(T_{f(b)})`, a `k`-block permutation.

**Capacity lifts.** Let `n` be monotone along `R(τ) ⊇ E`. Put `M_b = max_{P_b} n` and `m_c = min_{T_c} n`. Monotonicity
along `P_b × T_{f(b)}` gives `M_b <= m_{f(b)}`. Then

    Σ_A n = Σ_b Σ_{P_b} n <= k Σ_b M_b <= k Σ_b m_{f(b)} = k Σ_c m_c <= Σ_c Σ_{T_c} n = Σ_A n.

So all are equalities, and `n` takes one value `v_b` on `P_b ∪ T_{f(b)}`. The lift of the capacity-lift claim is
`Φ(y)(g) = (τ(x)(g), i_g)` on `B = {(a, i) : i < n(a)}`, so
`R(Φ) = {((a, i), (a', i)) : (a, a') ∈ R(τ), i < n(a)}`. It contains
`∪_b ∪_{i < v_b} (P_b × {i}) × (T_{f(b)} × {i})`. The domain blocks partition `B`, and so do the codomain blocks,
since `n = v_{f^(-1)(c)}` on `T_c`. This is a `k`-block permutation of `B`. The lift is injective, and it is strict iff
`τ` is: it is not surjective when `τ` is not (proof of the capacity-lift claim), and `r ∘ Φ = τ ∘ r` with `r` onto
shows that `Φ` surjective forces `τ` surjective.

**Overgroups.** For `G ≤ H`, the rule `μ` with memory `M ⊆ G ⊆ H` defines an automaton on `A^H` whose transition
digraph is `{(u(1), μ(u)) : u ∈ A^M}` again. Its value at `h` depends on `x|_{hM}` with `hM ⊆ hG`, so on
`A^H = Π_{hG ∈ H/G} A^{hG}` it acts coset by coset, each time as `τ` under `g ↦ hg`. So it is injective, resp.
surjective, iff `τ` is. `∎`

(Indexing. Only a bijection between the two sets of blocks matters: reindexing the codomain blocks along it turns
the index sets `{(b, i)}` and `{(c, i)}` into one set, as in the definition.)

## Item 4. Periodic classes

Let `τ` be injective. Every letter `c` lies on the cycle `c -> π(c) -> ... -> c` of `R(τ)`, since
`(c, π(c)) = (c^G(g), τ(c^G)(g))`. So every class contains a closed walk.

**Period and cyclic classes.** Let `D` be a class, `q` the gcd of the lengths of closed walks in `D`, and fix
`d_0 ∈ D`. For `d ∈ D` let `j(d)` be the length mod `q` of any walk `d_0 -> d` inside `D`. It is well defined: two
such walks of lengths `l_1, l_2`, followed by one walk `d -> d_0` of length `l_3`, give closed walks of lengths
`l_1 + l_3` and `l_2 + l_3`. Every edge inside `D` raises `j` by `1`. Put `D_j = j^(-1)(j)`.

**Walk lemma.** There is `N` such that for all `d, d' ∈ D` and all `n >= N` with `n ≡ j(d') - j(d) (mod q)`, some
walk of length exactly `n` runs from `d` to `d'` inside `D`.
- The lengths of closed walks at `d_0` form an additive semigroup `L_0`. Its gcd is `q`: it divides `q` because a
  closed walk `w` at any vertex `d`, prefixed by a walk `d_0 -> d` of length `α` and followed by a walk `d -> d_0` of
  length `β`, gives `α + β` and `α + |w| + β` in `L_0`. Conversely `q` divides every element of `L_0`.
- So `L_0` contains every multiple of `q` above some `N_0` (Schur, as in item 3 of the capacity-lift proof).
- Fix walks `d -> d_0` of length `α(d) ≡ -j(d)` and `d_0 -> d'` of length `β(d') ≡ j(d')`. For
  `n >= α(d) + β(d') + N_0` with `n ≡ j(d') - j(d)`, insert a closed walk at `d_0` of length `n - α(d) - β(d')`.
  Take `N` to be the maximum over the finitely many pairs.

**Balance.** A `π`-cycle through `c ∈ C` is a closed walk through `c`, so it lies in the class `C`. Hence `π`
restricts to an injection `C -> C` with `(c, π(c))` an edge inside `C`, so `π(C_i) ⊆ C_{i+1}` and
`|C_0| <= |C_1| <= ... <= |C_{p-1}| <= |C_0|`. All `|C_i|` equal `|C| / p`, and `p` divides `|C|`.

**Products.** Let `C` (period `p`, index `i`) and `D` (period `q`, index `j`) be classes of injective `τ` and `σ`,
and `h = gcd(p, q)`.
- A walk of length `n` in `R(τ) ⊗ R(σ)` is a pair of walks of length `n` (item 3). The projections of a closed walk
  are closed walks, so each class of the product lies in `C × D` for classes `C`, `D`.
- Put `W_r = {(c, d) ∈ C × D : i(c) - j(d) ≡ r (mod h)}`. Edges inside `C × D` keep `i - j mod h`, so no class meets
  two `W_r`.
- For `(c, d), (c', d') ∈ W_r`, the congruences `n ≡ i(c') - i(c) (mod p)` and `n ≡ j(d') - j(d) (mod q)` are
  compatible mod `h`, so by the Chinese remainder theorem they have arbitrarily large common solutions `n`. The walk
  lemma in both factors gives a walk of length `n` from `(c, d)` to `(c', d')`. So each `W_r` is strongly connected,
  and the classes of the product inside `C × D` are exactly `W_0, ..., W_{h-1}`.
- Size: `|W_r| = Σ_j |D_j| · (|C| / p) · |{i ∈ Z/p : i ≡ j + r (mod h)}| = |D| (|C| / p)(p / h) = |C||D| / h`.
- Valuations: `v_ℓ(h) <= min(v_ℓ(p), v_ℓ(q)) <= min(v_ℓ|C|, v_ℓ|D|)`, since `p | |C|` and `q | |D|`. So
  `v_ℓ(|C||D| / h) >= max(v_ℓ|C|, v_ℓ|D|)`. Minimizing over classes gives the claim. `∎`

## Item 5. The move set

Assign to each `Φ ∈ 𝓜` a block size `β(Φ)` with `R(Φ) ⊇` a `β(Φ)`-block permutation, by induction on the
construction.
- A far translate of a strict `τ` on `k` letters: `β = k` (item 2).
- A bijective automaton: `β = 1` (graph of `π`).
- Products: `β(Φ × Ψ) = β(Φ) β(Ψ)` (item 3).
- Letter permutations, capacity lifts, overgroup induction: `β` unchanged (item 3).
- A far translation of `Φ` on alphabet `B`: `β = |B|` (item 2). By item 1, `β(Φ)` divides `|B|`, since `B` is the
  union of classes.

**Invariant.** If `Φ` is strict, `β(Φ)` is divisible by the alphabet size of some strict automaton used at a leaf of
the construction.
- Leaves: a strict leaf is a far translate, with `β = k`. Bijective leaves are not strict.
- A product of injective automata is strict iff some factor is strict (item 3), and then `β` of that factor
  divides `β` of the product.
- Letter permutations, capacity lifts and overgroup induction keep strictness and `β` (item 3; for induction,
  strictness passes up and `R` is unchanged).
- A far translation keeps strictness (item 2) and replaces `β(Φ)` by `|B|`, a multiple of `β(Φ)`.

So for strict `Φ`, some leaf size `k_i` divides every class size of `R(Φ)` by item 1, and `g(Φ)` is a power of two
only if `k_i` is. `∎`
