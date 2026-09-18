---
rg: 2
id: finite-cycle-block-commutators-reduce-to-monodromy
kind: claim
title: A commutator with a finite block cycle can only change one block by a commutator with the cycle monodromy, so the finite analogue of the telescoping trick gives nothing
distinct_from:
  fp-simple-group-with-commutator-width-at-least-two: that records the AIM question, answered yes in the literature by Caprace--Fujiwara; this is an elementary structural lemma about which elements a single commutator with a block-cycling element can be, and it gives no bound on the commutator width of any group.
  equicontinuous-bs-bases-force-conjugator-entropy: that bounds the entropy of a conjugator realizing a Baumslag--Solitar relation; this computes the block components of a commutator of a block-preserving element with a block-cycling element, and uses no dynamics.
---

**ESTABLISHED** (elementary lane proof, written inline, not independently reviewed; no
priority claimed, and the statement may well be folklore).

## Statement

Let `X` be a set (for the intended use, a Cantor space and homeomorphisms), let
`A_0, …, A_{n-1}` be pairwise disjoint nonempty subsets (clopen in the intended use), and
put `A = A_0 ∪ … ∪ A_{n-1}`. Let

- `h` be a bijection of `X` with `h(A_i) = A_{i+1}` for all `i` mod `n`, and `h = id` off `A`;
- `Y` be a bijection of `X` with `Y(A_i) = A_i` for all `i`, and `Y = id` off `A`.

Write `h_i = h|_{A_i} : A_i → A_{i+1}` and `y_i = Y|_{A_i}`. Identify each block with the
first one along the cycle by `ι_0 = id` and `ι_i = h_{i-1} ∘ ⋯ ∘ h_0 : A_0 → A_i`, put
`ỹ_i = ι_i^{-1} y_i ι_i ∈ Sym(A_0)`, and let

    μ = h_{n-1} ∘ ι_{n-1} ∈ Sym(A_0)

be the **monodromy** of the cycle (`μ = h|_{A_0}` when `n = 1`).

Then `g = [Y, h] = Y h Y^{-1} h^{-1}` is supported in `A`, preserves every block, and

1. `ι_i^{-1} (g|_{A_i}) ι_i = ỹ_i ỹ_{i-1}^{-1}` for `1 ≤ i ≤ n-1`;
2. `g|_{A_0} = ỹ_0 · μ ỹ_{n-1}^{-1} μ^{-1}`;
3. consequently, if `g` is supported in `A_0` alone, then `ỹ_{n-1} = ỹ_0` and

       g|_{A_0} = [ỹ_0, μ].

   In particular, if the cycle is untwisted (`μ = id`), then `g = 1`.

## Proof

Both `Y` and `h` are the identity off `A`, so `g` is too. For `p ∈ A_i` we have
`h^{-1}(p) ∈ A_{i-1}`, then `Y^{-1}` keeps it in `A_{i-1}`, then `h` sends it to `A_i`, and
`Y` keeps it there; so `g(A_i) = A_i` and

    g|_{A_i} = y_i ∘ (h_{i-1} y_{i-1}^{-1} h_{i-1}^{-1}).

Since `ι_i = h_{i-1} ι_{i-1}`, we get `ι_i^{-1} h_{i-1} = ι_{i-1}^{-1}`, hence for
`1 ≤ i ≤ n-1`

    ι_i^{-1} (h_{i-1} y_{i-1}^{-1} h_{i-1}^{-1}) ι_i
      = ι_{i-1}^{-1} y_{i-1}^{-1} ι_{i-1} = ỹ_{i-1}^{-1},

which is item 1. For `i = 0` the wrap-around map is `h_{n-1} : A_{n-1} → A_0`, and
`h_{n-1} y_{n-1}^{-1} h_{n-1}^{-1} = μ ỹ_{n-1}^{-1} μ^{-1}` because
`h_{n-1} = μ ι_{n-1}^{-1}`; that is item 2.

For item 3, suppose `g|_{A_i} = id` for `1 ≤ i ≤ n-1`. Multiplying the relations of item 1
in the order `i = n-1, n-2, …, 1` telescopes:

    1 = (ỹ_{n-1} ỹ_{n-2}^{-1})(ỹ_{n-2} ỹ_{n-3}^{-1}) ⋯ (ỹ_1 ỹ_0^{-1}) = ỹ_{n-1} ỹ_0^{-1},

so `ỹ_{n-1} = ỹ_0`, and item 2 becomes `g|_{A_0} = ỹ_0 μ ỹ_0^{-1} μ^{-1} = [ỹ_0, μ]`. ∎

## What it says about the width-one program

The first two items of AIM *Groups of dynamical origin* Problem 3.1 ask for `ρ_1 = 1`, that
is, for every element of `F`, `T`, `V` or a topological full group to be a single
commutator. For a group of homeomorphisms whose elements have finitely many pieces, the
classical proof of width one is unavailable: it writes `g` as `[∏_{k ≥ 0} h^k g h^{-k}, h]`
for an `h` with the `h^k(A)` pairwise disjoint, and that infinite product has infinite
support, so it is not an element of `V` or of any `nV`.

The lemma above says the obvious finite repair cannot work. If one replaces the infinite
disjoint chain by a finite cycle of blocks and a block-preserving `Y`, then the resulting
commutator changes one block only by a commutator with the monodromy of the cycle. So:

- an untwisted finite cycle produces nothing at all (item 3);
- a twisted one only reduces "`g` is a commutator in the host" to "`g|_{A_0}` is a
  commutator in `Sym(A_0)`, with one factor the monodromy", which is the same kind of
  statement one started with.

So a proof of `ρ_1 = 1` for these groups must use an element `Y` that does **not** preserve
the blocks of its partner, or a partner that is not a pure cycle on blocks.

## Scope

- The lemma constrains only commutators `[Y, h]` of the stated shape. It is **not** a lower
  bound on the commutator width of `V`, of any `nV`, or of any other group: other pairs
  `(Y, h)` are unconstrained, and nothing here says any element fails to be a commutator.
- No topology, measure or finiteness is used; `X` may be any set and `Y`, `h` any bijections
  of the stated shape. In the intended application `Y` and `h` are elements of a group of
  homeomorphisms with finitely many pieces, and `A_i` are clopen.
- The calibration `n = 1` is the tautology `g = [y_0, h|_{A_0}]`.
