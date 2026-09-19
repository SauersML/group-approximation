---
rg: 2
id: block-permutation-transitions-force-divisible-classes
kind: claim
title: A transition digraph that contains a k-block permutation has every class size divisible by k, and letter-level moves on strict automata never leave that situation, so they cannot lower the odd part of g(τ)
distinct_from:
  transition-digraph-capacity-lifts-give-nonsurjunctive-sizes: that turns class sizes into nonsurjunctive sizes and notes that identity layers and capacity lifts keep certified sizes in g(τ)Z; this proves a divisibility invariant for a much larger move set (products with arbitrary injective automata, letter permutations on both sides, far translations, capacity lifts, overgroup induction) and shows g(τ) is not a translation invariant.
  strict-automata-reach-power-residue-donor-types: that is the open bridge at the level of donor types; this is an obstruction to every letter-level route to it, not a proof or refutation of it.
  full-shifts-with-different-alphabets-are-not-conjugate: that uses the constant permutation to compare alphabet sizes; this uses the same permutation inside one alphabet, to balance periodic transition classes.
artifacts:
  - experiments/transition-class-splitting-2026-09-17/search.py
  - experiments/transition-class-splitting-2026-09-17/check_blocks.py
---

**ESTABLISHED** by `block-permutation-transitions-force-divisible-classes-proof` (elementary, no imports).

**Setting.** Notation as in `transition-digraph-capacity-lifts-give-nonsurjunctive-sizes`: `τ(x)(g) = μ((g^(-1)x)|_M)`
with `1 ∈ M`, transition digraph `R(τ) = {(u(1), μ(u)) : u ∈ A^M}`, classes are its strongly connected components,
`g(τ)` is the gcd of the class sizes. If `τ` is injective, `τ(c^G) = π(c)^G` for a permutation `π` of `A`.

- A **k-block permutation** of `A` is a relation `E = ∪_{b ∈ I} P_b × T_{f(b)}`, where `A = ⊔_b P_b = ⊔_c T_c` are two
  partitions of `A` into `k`-element sets, indexed by one set `I`, and `f : I -> I` is a bijection.
- `τ` has **block size k** if `R(τ)` contains a `k`-block permutation. Every injective `τ` has block size `1`, since
  `R(τ)` contains the graph of `π`.
- The **translate** `T_s ∘ τ`, with `T_s(y)(g) = y(gs)`, is **far** if `s ∉ M^(-1)`.

**Theorem.**
1. **Divisibility.** If `R ⊆ A × A` contains a `k`-block permutation, then every letter lies on a cycle of `R`, and
   every class of `R` has size divisible by `k`. So `k | g`.
2. **Far translates are complete.** If `G` is infinite and `τ` is injective, then for every `s ∉ M^(-1)` the far
   translate `T_s ∘ τ` has `R(T_s ∘ τ) = A × A`. It is strict iff `τ` is. So every strict automaton on `k` letters
   has a strict translate of block size `k`. In particular `g` is not invariant under composition with bijective
   automata: `T_s^(-1) ∘ T_s ∘ λ = λ` for a letter permutation `λ` takes `g = |A|` to the gcd of the `λ`-orbit sizes.
3. **Closure.** Let `τ`, `σ` be injective with block sizes `k`, `k'`.
   - `τ × σ` has block size `k k'`, since `R(τ × σ) = R(τ) ⊗ R(σ)`, the tensor product of digraphs.
   - `λ ∘ τ ∘ λ'` has block size `k` for letter permutations `λ`, `λ'`.
   - Every capacity lift of `τ` (item 1 of the capacity-lift claim) has block size `k`: a capacity is constant on
     each `P_b ∪ T_{f(b)}`.
   - The automaton with the same local rule over an overgroup `H ≥ G` has the same transition digraph.
4. **Periodic classes are balanced.** Let `τ` be injective and let `C` be a class of `R(τ)` of period `p`, with cyclic
   classes `C_0, ..., C_{p-1}`. Then `|C_i| = |C| / p` for all `i`. If `D` is a class of an injective `σ`, of period
   `q`, the classes of `R(τ × σ)` inside `C × D` are exactly `h = gcd(p, q)` sets of size `|C||D| / h`. So for every
   prime `ℓ`, `v_ℓ(g(τ × σ)) >= max(v_ℓ(g(τ)), v_ℓ(g(σ)))`, with no translation needed.
5. **Obstruction to letter-level bridges.** Let `𝓜` be the smallest set of automata containing the far translates
   of strict automata and all bijective automata, and closed under products, letter permutations on either side,
   capacity lifts, far translations and overgroup induction. Then every strict `Φ ∈ 𝓜` has a block size divisible
   by the alphabet size of one of the strict automata it was built from. Hence, if none of those alphabet sizes is a
   power of two, no strict member of `𝓜` has `g(Φ)` a power of two. The certificate of item 3 of
   `transition-digraph-capacity-lifts-give-nonsurjunctive-sizes`, which needs `g` to be a power of two, then never
   applies.

**Why it matters.** By item 5 of the capacity-lift claim, the bridges `some-nonsurjunctive-group-gives-a-binary-power-one`
and `strict-automata-reach-power-residue-donor-types` are both exactly the question whether some strict automaton
has `g(τ)` a power of two. This claim kills every route to that bridge that manipulates letters and products.
- **Invariant.** The block size, a `k`-block permutation inside `R`.
- **Where every member dies.** At item 1, the line-digraph count: `E` is the line digraph of a `k`-in, `k`-out regular
  multigraph, whose components are strongly connected with `k` arcs per vertex.
- **What survives.** Only moves that shrink `R` by cancellation between correlated sites:
  - compositions `β ∘ τ` with bijective `β` whose memory overlaps that of `τ` (a near translation already undoes a
    far one, item 2);
  - powers `τ^p` with `R(τ^p) ⊊ R(τ)^p`;
  - restriction to a finite-index subgroup, where the tuple digraph is a proper subset of `R^{⊗m}`;
  - restriction to an upset `U` on which `τ` stays strict;
  - rules that are not products.
- **Consequence.** A witness for the bridge must be a strict automaton whose sitewise transitions are much sparser
  than those of its own far translate, which is complete. Writing `g(τ)` as a function of `τ` alone hides that it
  is really a statement about how local a strict automaton can be made by bijective recoding.
- **Checks.** `check_blocks.py` checks items 1, 3 (letter permutations of `K_k ⊗ S`, `S` containing a permutation) and
  the capacity constancy on random instances, and shows that without a permutation in `S` the count fails.
  `search.py` shows that random letter permutations of `K_3 ⊗ S` merge everything, for `S` a shear digraph.
