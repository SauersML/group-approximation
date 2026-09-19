---
rg: 2
id: monotone-automata-with-a-pinned-bracketing-star-are-onto-proof
kind: route
title: Bound the automaton above by a configuration in a rigid up-set to preserve one letter, then apply unit-charge noncreation
target: monotone-automata-with-a-pinned-bracketing-star-are-onto
requires:
  - monotone-injective-chain-automata-are-translations
  - finite-injective-charge-noncreation-forces-surjectivity
artifacts:
  - experiments/monotone-connected-posets-2026-09-17/search_z_results.txt
---

Complete proof. Automata act by `ρ(x)(h) = μ((x(hm))_{m ∈ M})` with `M ⊆ G` finite, and `G` acts by
`(g·x)(h) = x(g^{-1}h)`. For `t ∈ G` the map `σ_t(x) = x_t`, `x_t(h) = x(ht)`, is a bijective automaton with memory
`{t}`. It is monotone for any order. Since `σ_t(σ_s(x))(h) = x(hts)`, we have `σ_t σ_s = σ_{ts}` and
`σ_t^{-1} = σ_{t^{-1}}`.

## Step 0. Constants may be assumed fixed

`ρ` maps constants to `G`-invariant configurations, which are constants. It is injective, so it permutes the
constants by a permutation `π` of `L`. Some power `ρ^k` has `π^k = id`. `ρ^k` is monotone and injective, and if
`ρ^k` is surjective then so is `ρ`. The subshifts below are defined by the order alone, so from now on `ρ` fixes
every constant.

For a letter `c`, the subshift `(↑c)^G` is `{x : x >= c^G}`. For `x` in it, `ρ(x) >= ρ(c^G) = c^G`. So `(↑c)^G` is
`ρ`-invariant, and likewise `(↓c)^G` and every interval `[a,b]^G`. The restriction is an automaton with memory `M` on
that sub-alphabet: every pattern over the sub-alphabet extends to a configuration of the subshift, so the rule maps
such patterns into the sub-alphabet. The restriction is monotone, injective and fixes constants.

## Step 1. Item 1: one preserved letter

Let `τ' = σ_{t^{-1}} ∘ τ`, so `τ'(x)(h) = τ(x)(ht^{-1})`. It is an injective automaton with memory `t^{-1}M`, it
fixes `q^G`, and by hypothesis `x(h) = q` implies `τ'(x)(h) = q`. Also `τ'` is surjective iff `τ` is.

Apply `finite-injective-charge-noncreation-forces-surjectivity` with quiescent symbol `0 := q` and charge `w(a) = 1`
for every `a != q`. Its hypotheses are quoted there: "tau:A^G->A^G be a cellular automaton fixing 0^G ... Suppose
tau is injective on finitely supported configurations and W(tau(x)) <= W(x) for every finite x. Then equality holds
for every finite x. Moreover, ... is surjective on A^G."
- `τ'` fixes `q^G`, and it is injective on all of `L^G`, so also on finitely supported configurations.
- Let `x` be finitely supported, that is `x = q` off a finite set `F`. If `hM' ∩ F = ∅` for the memory `M'` of `τ'`,
  then `τ'(x)(h) = τ'(q^G)(h) = q`. So `τ'(x)` is finitely supported. Its support `S(τ'x)` is contained in
  `S(x) = {h : x(h) != q}` by preservation. Hence `W(τ'x) = |S(τ'x)| <= |S(x)| = W(x)`.

So `τ'` is surjective, and `W(τ'x) = W(x)`. A finite set contained in another of the same size equals it, so
`S(τ'x) = S(x)` for every finitely supported `x`.

For arbitrary `x` and `h`, let `x'` agree with `x` on `hM' ∪ {h}` and equal `q` elsewhere. Then
`τ'(x')(h) = τ'(x)(h)` and `x'(h) = x(h)`, and `S(τ'x') = S(x')` gives: `τ'(x)(h) = q` iff `x(h) = q`. In terms of
`τ` this reads `τ(x)(ht^{-1}) = q` iff `x(h) = q`. This proves item 1.

## Step 2. Item 2: pinned posets

*Chains.* A monotone injective automaton on a chain is `x ↦ x_t` by `monotone-injective-chain-automata-are-translations`,
whose theorem reads: "Then there is `t ∈ G` with `ρ(x)(h) = x(ht)` for all `x` and `h`."

*`⊥ + A`.* Let `K = {⊥} ∪ A`, where `⊥ < a` for all `a ∈ A` and `A` is an antichain. Let `ρ` be monotone,
injective and constant-fixing on `K^G`. If `|A| = 1`, `K` is a chain. Otherwise, for each `a ∈ A` the pair
`[⊥,a] = {⊥,a}` is a chain interval, so by Step 0 and the chain theorem, `ρ(x) = x_{t_a}` on `{⊥,a}^G`.

The translations agree. Take `a != b` in `A` and a site `s`.
- `u = a^G` except `⊥` at `s` lies in `{⊥,a}^G`. So `ρ(u)(h) = u(ht_a)`, which is `a` except at `h = st_a^{-1}`.
- `u' = a^G` except `b` at `s` satisfies `u' >= u`. So `ρ(u')(h) >= a`, hence `ρ(u')(h) = a` (as `a` is maximal),
  for every `h != st_a^{-1}`.
- `v = ⊥^G` except `b` at `s` lies in `{⊥,b}^G`, and `u' >= v`. So `ρ(u')(st_b^{-1}) >= ρ(v)(st_b^{-1}) = b`, and
  `ρ(u')(st_b^{-1}) = b != a`.

So `st_b^{-1} = st_a^{-1}`, that is `t_a = t_b =: t`.

Let `τ = σ_{t^{-1}} ∘ ρ`. It is monotone, injective, constant-fixing, and it is the identity on every `{⊥,a}^G`. If
`x(h) = a ∈ A`, the configuration `e = ⊥^G` except `a` at `h` satisfies `e <= x`. So `τ(x)(h) >= τ(e)(h) = a`, hence
`τ(x)(h) = a`. Item 1 with `q = a` and translation `1` gives: `τ(x)(h) = a` iff `x(h) = a`. So if `x(h) = ⊥`, then
`τ(x)(h)` is no letter of `A`, hence `τ(x)(h) = ⊥`. So `τ = id` and `ρ = σ_t`, that is `ρ(x) = x_t`.

*`A + ⊤`.* An automaton is monotone for `K` iff it is monotone for the reversed order `K^op`, and
`(A + ⊤)^op = ⊥ + A`. Being pinned is therefore invariant under order reversal. This proves item 2.

## Step 3. Item 3: the bracket criterion

By Step 0, `(↑m)^G` is invariant, and the restriction of `ρ` is monotone, injective and constant-fixing. As `↑m` is
pinned, there is `t` with `ρ(y) = y_t` for every `y ∈ (↑m)^G`.

Let `x(h) = m`. Put `y(h) = m`, and for `g != h` let `y(g)` be a common upper bound of `x(g)` and `m`, which exists
by hypothesis. Then `y >= x` sitewise and `y ∈ (↑m)^G`. By monotonicity,

    ρ(x)(ht^{-1}) <= ρ(y)(ht^{-1}) = y(h) = m,

and `m` is minimal, so `ρ(x)(ht^{-1}) = m`. So the hypothesis of item 1 holds for `τ = ρ`, `q = m` and this `t`,
with `ρ(m^G) = m^G` by Step 0. Hence `ρ` is surjective, and so is the original automaton, by Step 0.

For the dual statement, apply this to the reversed order `L^op`. `ρ` is monotone for it, a maximal `q` becomes
minimal, `↓q` becomes `↑q`, and pinnedness is invariant under reversal by Step 2. This proves item 3.

## Step 4. Corollaries

- *Height one.* Let `L` be connected with `|L| >= 2` and every letter minimal or maximal. Suppose a minimal `m` lies
  below every maximal letter. Then `↑m = {m} ∪ Max(L)`, which is `⊥ + A` with `A = Max(L)` an antichain, so it is
  pinned. A maximal letter `c` is a common upper bound of itself and `m`. By connectivity a minimal `m'` has an upper
  neighbour `c`, and `c >= m`. So item 3 applies. The case of a maximal letter above every minimal one is dual.
  - `K_{p,q}` satisfies this.
  - A fence of three letters is `V` or `Λ`. The fence `a < c > b < d` has `b` below both tops.
  - The fence `a < c > m < d > a'` has `m` below both tops. The fence `c > m < c' > m' < c''` has `c'` above both
    minima.
- *Chain up-set under a top.* If `L` has a greatest letter `⊤` and a minimal `m` with `↑m` a chain, then `↑m` is
  pinned, and `⊤` is a common upper bound for every letter. The dual case is the same.
- *Antichain up-set.* If `↑m \ {m}` is an antichain `A` of maximal letters and every letter lies below some letter of
  `A`, then `↑m = ⊥ + A` is pinned, and item 3 applies.

The artifact records the window-2 census over `Z` (`search_z.py`), which agrees on every poset it covers. It is a
check, not part of the proof.
