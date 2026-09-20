---
rg: 2
id: monotone-strict-automata-ascend-along-poset-homs-proof
kind: route
title: Apply the automaton to each member of an order-preserving family, and pass to components through zigzags of comparable configurations
target: monotone-strict-automata-ascend-along-poset-homs
requires:
  - monotone-injective-chain-automata-are-translations
  - monotone-binary-injective-rules-are-copies
artifacts:
  - experiments/monotone-poset-ascent-2026-09-17/chain_search_results.txt
---

Complete proof. Automata act by `ρ(x)(h) = μ((x(hm))_{m ∈ M})` with `M` finite. Configurations in `L^G` are
ordered sitewise. `ρ` is monotone.

## Item 1. Ascent

A configuration `x ∈ Hom(P,L)^G` is the same thing as a family `(x_p)_{p ∈ P}` in `L^G` with `x_p <= x_q` whenever
`p <= q`, via `x_p(g) = x(g)(p)`. Put `ρ_P(x)_p = ρ(x_p)`.
- *Well defined.* If `p <= q` then `x_p <= x_q`, so `ρ(x_p) <= ρ(x_q)` by monotonicity. So `ρ_P(x)(g)` is order
  preserving on `P`.
- *Automaton.* `ρ_P(x)(h)(p) = μ((x(hm)(p))_m)`, so `ρ_P(x)(h)` depends only on `x|_{hM}`, through the rule
  `μ_P(φ)(p) = μ((φ(m)(p))_m)` on `Hom(P,L)^M`. It is `G`-equivariant with memory `M`.
- *Injective.* `ρ_P(x) = ρ_P(y)` gives `ρ(x_p) = ρ(y_p)` for every `p`, so `x_p = y_p` since `ρ` is injective.
- *Not surjective.* Pick `z ∈ L^G` not in `ρ(L^G)`. The constant family `z_p = z` is order preserving, so it is a
  configuration of `Hom(P,L)^G`. A preimage `x` would give `ρ(x_p) = z`, which is impossible.

So `|Hom(P,L)| ∈ NS(G)`.

*Counts.*
- `L = {0 < 1}`: `f ↦ f^{-1}(0)` is a bijection from `Hom(P,L)` onto the down-sets of `P`. The chain of `n-1`
  elements has `n` down-sets, so every `n >= 2` occurs.
- `L` a chain of `k` letters, `P` a chain of `j` elements: order-preserving maps are nondecreasing sequences of length
  `j` in `k` letters, and there are `C(k+j-1, j)` of them. `k = j = 3` gives `10`. A disjoint union of posets
  multiplies the counts.
- `L` an antichain: `p <= q` forces `f(p) = f(q)`, so `f` is constant on each component of `P`, and every such
  choice is order preserving. That gives `|L|^c`.

## Item 2. Chains are dead

This is `monotone-injective-chain-automata-are-translations`: a monotone injective automaton on a chain is a copy of
one coordinate, so it is surjective. No monotone strict automaton on a chain exists.

## Item 3. Chain intervals are rigid

`ρ` sends constants to `G`-invariant configurations, which are constants. It is injective, so it permutes the
constants through a permutation `σ` of `L`. By monotonicity, `a <= b` implies `σ(a) <= σ(b)`. So some power `σ^m` is
the identity. `ρ^m` is monotone and injective. It is strict when `ρ` is, since `ρ^m(L^G) ⊆ ρ(L^G)`. Replace `ρ` by
`ρ^m`, so that `ρ(c^G) = c^G` for every `c`.

For `a <= b` let `[a,b] = {c : a <= c <= b}`. Then `x ∈ [a,b]^G` iff `a^G <= x <= b^G`, which gives
`a^G = ρ(a^G) <= ρ(x) <= ρ(b^G) = b^G`. So `[a,b]^G` is `ρ`-invariant. The restriction is an automaton with memory
`M`: its rule is `μ` on `[a,b]^M`, and it takes values in `[a,b]`, because every pattern extends to a configuration
of `[a,b]^G`. The restriction is monotone and injective. If `[a,b]` is a chain it is a copy of one coordinate, by
`monotone-injective-chain-automata-are-translations`. For a covering pair `a ⋖ b` we have `[a,b] = {a,b}`, and the
restriction is a copy by `monotone-binary-injective-rules-are-copies`.

## Item 4. Reduction to collapse lifts

Let `L_1, ..., L_s` be the connected components of the comparability graph of `L`, and `r : L -> π_0(L)` the
quotient.

*Claim.* If `r ∘ x = r ∘ y` then `r ∘ ρ(x) = r ∘ ρ(y)`.

Proof. Fix `h`, and list `hM = {g_1, ..., g_n}`. For each `i`, `x(g_i)` and `y(g_i)` lie in one component, so there
is a path `x(g_i) = c_0, c_1, ..., c_ℓ = y(g_i)` with `c_{j-1}` and `c_j` comparable. Change the value at `g_1` along
its path one step at a time, then at `g_2`, and so on, leaving every site outside `hM` equal to `x`. Consecutive
configurations differ at one site, where the two values are comparable, so they are comparable sitewise. By
monotonicity their images at `h` are comparable, hence in one component. The last configuration agrees with `y` on
`hM`, so its image at `h` is `ρ(y)(h)`. So `r(ρ(x)(h)) = r(ρ(y)(h))`.

Fix a section `s : π_0(L) -> L` of `r`, and put `τ̄(u) = r ∘ ρ(s ∘ u)`. This is an automaton with memory `M` and rule
`r ∘ μ ∘ s^M`. For any `x`, `s ∘ r ∘ x` and `x` have the same components sitewise, so the claim gives
`r ∘ ρ = τ̄ ∘ r`.

Now let `P` be connected. If `p` and `q` are comparable, so are `f(p)` and `f(q)`. So an order-preserving `f` maps a
path in `P` to a path in `L`, and its image lies in a single component. Hence `Hom(P,L) = ⊔_i Hom(P, L_i)`, and each
part is nonempty because it contains the constants. Let `R : Hom(P,L) -> π_0(L)` send `f` to the component
containing its image. For `x ∈ Hom(P,L)^G` and any `p ∈ P` we have `R ∘ x = r ∘ x_p`. So

    R(ρ_P(x)(g)) = r(ρ(x_p)(g)) = τ̄(r ∘ x_p)(g) = τ̄(R ∘ x)(g),

that is, `R ∘ ρ_P = τ̄ ∘ R`. So `ρ_P` is a letter-collapse lift of `τ̄`, in the sense of
`collapse-lifts-with-unique-largest-fiber-are-surjective`, with fibers of sizes `|Hom(P, L_i)|`. This proves item 4.

## Remarks

- When `τ̄` is injective and one `|Hom(P, L_i)|` is strictly largest, the collapse-lift theorem gives: that size is in
  `NS(G)`, or `ρ_P` is surjective. Item 1 says `ρ_P` is not surjective. So in that case the largest fiber size
  `|Hom(P, L_i)|` must already lie in `NS(G)`, which is a strong constraint on the pair `(ρ, P)`.
- When `L` is connected, `π_0(L)` has one point and item 4 carries no information. That is the Boolean-square
  survivor named in the claim.
