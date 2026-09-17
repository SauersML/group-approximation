---
rg: 2
id: thompson-f-p22-no-private-pivot-order-proof
kind: route
title: The order-minimum of a stubborn set has one private point; peeling finds the maximal stubborn set, and König's lemma gives the converse
target: thompson-f-p22-monomials-admit-no-private-pivot-order
requires:
  - thompson-f-private-pivot-orders-give-doubling-and-non-ore-pairs
artifacts:
  - experiments/thompson-f-2026-09-17/stubborn_core.cpp
  - experiments/thompson-f-2026-09-17/verify_stubborn_core.py
  - experiments/thompson-f-2026-09-17/s35_stubborn_core_D7.txt
  - experiments/thompson-f-2026-09-17/stubborn_census.jsonl
---

Notation as in the claim. The required claim is used only for its definitions and for the fact,
proved in its route, that `N(w)` is finite, so `m_<(w)` is defined. Every `m ∈ N(w)` has degree
`deg w − d`, so privacy in layer `M_D` depends only on the order restricted to `M_D`.

**Item 1.** Let `Z` be stubborn and `<` a total order on `M`. Let `z = min Z`, and let `w` be private for
`z`. Then every `m ∈ N(w)` satisfies `m <= m_<(w) = z`, while every `m ∈ Z` satisfies `m >= z`. So
`N(w) ∩ Z = {z}`. By stubbornness there is at most one such `w`, so `z` has at most one private point.

**Union closure and peeling.**
- *Unions.* Let `Z_1, Z_2` be stubborn and `z ∈ Z_1`. If `N(w) ∩ (Z_1 ∪ Z_2) = {z}`, then
  `N(w) ∩ Z_1 = {z}`, so at most one `w ∈ S z` qualifies. The same holds for `z ∈ Z_2`.
- *Peeling.* Call `z` *free* in a finite set `A ∋ z` if at least two `w ∈ S z` have `N(w) ∩ A = {z}`.
  Peeling starts from `A = Y` and deletes free points until none is left.
- *Peeling never deletes a stubborn point.* If `Z ⊆ A` is stubborn and `z ∈ Z`, every `w` with
  `N(w) ∩ A = {z}` also has `N(w) ∩ Z = {z}`, so `z` is not free in `A`.
- *The survivor set is stubborn.* No survivor is free in it.

So the survivor set is the largest stubborn subset `core(Y)`, whichever order of deletions is used.
`stubborn_core.cpp` implements this with predecessor lists. `N(w)` is taken inside `Y`, which is
legitimate because stubbornness of `Z ⊆ Y` refers only to `N(w) ∩ Z`.

**Item 3.** Let `z_1, z_2, ..., z_n` be the peeling order of `Y`, and put `A_k = {z_k, ..., z_n}`.
- Each `z_k` has two successors `w` with `N(w) ∩ A_k = {z_k}`.
- Such a `w` has no predecessor in `A_(k+1)`, so it cannot be counted again at a later step.
- If `core(Y) = ∅`, the peeling removes all of `Y`, giving `2|Y|` distinct points of `S Y`.
- Hence `|S Y| < 2|Y|` forces `core(Y) ≠ ∅`.

**Item 2.** "Only if" is item 1. For "if", suppose no `M_D` has a stubborn subset.
- *Setup.* Fix `D`. The layer `M_D` is countable. Choose finite `Y_1 ⊆ Y_2 ⊆ ...` with union `M_D` and
  `N(S Y_n) ⊆ Y_(n+1)`, which is possible because `N(w)` is finite.
- *Finite approximations.* Let `O_n` be the set of total orders on `Y_(n+1)` under which every `z ∈ Y_n`
  has two private points `w ∈ S z`. This condition makes sense because `N(w) ⊆ Y_(n+1)`.
- *`O_n` is nonempty.* Since `core(Y_(n+1)) = ∅`, peel `Y_(n+1)` as `z_1, z_2, ...` and set
  `z_1 < z_2 < ...`. Then `z_k` has two `w` with `N(w) ∩ A_k = {z_k}`. All other points of `N(w)` were
  deleted earlier, so they are smaller, and `m_<(w) = z_k`.
- *Compatibility.* Restricting an order in `O_(n+1)` to `Y_(n+1)` lands in `O_n`, because privacy for
  `z ∈ Y_n` only compares points of `Y_(n+1)`.
- *Limit.* Each `O_n` is finite and nonempty, so by König's lemma there is a compatible sequence
  `o_n ∈ O_n`. Their union is a total order on `M_D` under which every `m` has two private points.
- *Assembling `M`.* Order the layers `M_0 < M_1 < ...` and use these orders inside each layer. Privacy
  is layer-internal, so this is a pivot order.

Any stubborn subset of `M_D` is finite, so it lies in some `M_(D,L)`. Hence a pivot order exists iff
`core(M_(D,L)) = ∅` for all `D, L`.

**Item 4 (computation).** `stubborn_core 7 10 "0,0;0,1;0,2;0,3;1,1;1,2;1,3;2,2;2,3"` runs in under a second.
1. It enumerates `M_(7,10)` (19448 normal forms) and computes all `s m` by the insertion rule.
2. Its self-test checks the relations and associativity on 20000 random triples, and checks left
   cancellation `s m ≠ s' m`.
3. After peeling, it re-verifies stubbornness of the survivors twice: once from the predecessor arrays,
   and once by recomputing every product from words into a fresh `std::map`.
4. It writes `Z` to `s35_stubborn_core_D7.txt`.

`verify_stubborn_core.py` then checks `Z` without using normal-form arithmetic at all.
- It realizes `x_0, x_1` as PL homeomorphisms with exact integer breakpoints over `2^256` and
  `x_i = x_0^(−1) x_(i−1) x_0`.
- It asserts `x_j x_i = x_i x_(j+1)` for `i < j <= 6`. So `i ↦ x_i` induces a monoid map `M → F`,
  injective because `M` embeds in `F`, and equal PL maps mean equal elements of `M`.
- It asserts that `Z` consists of 1092 distinct normal forms of degree 7.
- It computes the 9828 products `s z` as PL maps and counts, for each `w`, the `z ∈ Z` with
  `w ∈ S z`. The histogram of `Z`-private counts is `{1: 1092}`, and `|S Z| = 5304`.

So `Z` is stubborn for `S_(3,5)`, and item 1 gives the headline. The empty cores for smaller `D` and
`L`, and the census table, come from the same program. They are data and are not needed for the
headline.
