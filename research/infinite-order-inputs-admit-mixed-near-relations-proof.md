---
rg: 2
id: infinite-order-inputs-admit-mixed-near-relations-proof
kind: route
title: Match the right cosets of the infinite cyclic subgroup with the product case, then reuse the route-form permutation
target: infinite-order-inputs-admit-mixed-near-relations
requires:
  - route-form-shell-inputs-have-computable-mixed-near-relations
---

Notation as in the target. Put `P_1 = Z x <u>` with `u` of infinite order, the input of
`route-form-shell-inputs-have-computable-mixed-near-relations` for `P_0 = Z`. That node
gives, in its item 1, a bijection `nu_1 : P_1 -> N` with `nu_1(u·y) = λ'(nu_1(y))` for all
`y ∈ P_1`. By its item 3 `nu_1` is computable with computable inverse, since `Z` has
decidable word problem.

**Step 1: a coset bijection `β : P -> P_1`.**
- The orbits of left multiplication by `t` on `P` are the right cosets `<t>h`. Each is
  a free `Z`-orbit, since `t` has infinite order.
- There are countably infinitely many of them, because `P` is countable and
  `[P : <t>] = ∞`.
- Choose representatives `h_0, h_1, h_2, …`, one per right coset, and put
  `β(t^k h_i) = (i, u^k)`.
- `β` is a bijection, because each element of `P` is `t^k h_i` for exactly one pair
  `(i, k)`. It satisfies `β(t g) = u β(g)` for all `g ∈ P`.

**Step 2: item 1.** Put `nu = nu_1 ∘ β`. Then
`nu(t g) = nu_1(u β(g)) = λ'(nu_1(β(g))) = λ'(nu(g))`, so `λ_t = λ'`.

**Step 3: item 2.**
- The relation `[λ' s^4 λ'^-1, s^8] = 1` in `NearSym(N)` is item 2 of the route-form
  node. It is a statement about the two permutations `λ'` and `s` alone, so it holds
  for `λ_t = λ'`.
- Since `t ≠ 1`, the word `t s^4 t^-1 s^8 t s^-4 t^-1 s^-8` alternates between
  nontrivial letters of the free factors `P` and `<s>`. It is therefore reduced and
  nontrivial in `P * <s>`, yet it maps to `1` in `R_nu`.

**Step 4: item 3.**
- Enumerate `P` using its decidable word problem. Declare an element to be a new
  representative `h_i` when the power problem shows that `g h_j^-1 ∉ <t>` for every
  earlier `h_j`.
- For a given `g`, run the enumeration until some `h_j` has `g h_j^-1 = t^k`. The
  power problem returns `k`, so `β(g) = (j, u^k)` is computed.
- Conversely `β^-1(i, u^k) = t^k h_i`.
- Composing with the computable `nu_1` and `nu_1^-1` gives `nu` and `nu^-1`.
