---
rg: 2
id: fp-tree-groups-have-computable-faithful-tree-actions-proof
kind: route
title: Enumerate all truncated-tree representations and hang the i-th one below the vertex 1^i 0
target: fp-tree-groups-have-computable-faithful-tree-actions
requires: []
---

Self-contained proof.

**Notation.**
- `A_n` is the automorphism group of the finite truncated tree `X^{<=n}`. It is
  finite.
- `r_n : Aut(T_d) -> A_n` is restriction.
- `e_n : A_n -> Aut(T_d)` is extension by trivial sections:
  `e_n(a)(uv) = a(u) v` for `|u| = n`, and `e_n(a)(u) = a(u)` for `|u| <= n`.
  Both `r_n` and `e_n` are homomorphisms.

**Step 1 (enumeration).** Enumerate all pairs `(n, f)` with `n >= 0` and a map
`f : S -> A_n` such that every relator in `R`, evaluated under `f`, is `1` in
`A_n`. Each check is a finite computation in the finite group `A_n`, so the list
is computably enumerable. For each `n` the trivial map qualifies, so the list is
infinite. Write it as `rho_0, rho_1, rho_2, ...` with `rho_i : G -> A_{n_i}`.
Each `rho_i` is a homomorphism because `R` is the full set of defining relators.

**Step 2 (the action).** Every vertex of `T_d` is either `1^i` or `1^i 0 w`
with `i >= 0` and `w in X^*`, and not both. For `g in G` put

```text
tau(g)(1^i)     = 1^i,
tau(g)(1^i 0 w) = 1^i 0 e_{n_i}(rho_i(g))(w).
```

The map `tau(g)` fixes the ray `1^infinity` and preserves each cone
`1^i 0 X^*`, acting on it as `e_{n_i}(rho_i(g))`. It therefore preserves length
and prefixes, and it is bijective. So `tau(g) in Aut(T_d)`, and `tau` is a
homomorphism, because on each cone it is the composite homomorphism
`e_{n_i} o rho_i`.

**Step 3 (computability).** To compute `tau(s)(w)`:
- read `i` from the prefix of `w`;
- run the enumeration of Step 1 until `rho_i` appears;
- apply the finite permutation `rho_i(s)` to the first `n_i` letters after
  `1^i 0`.

The algorithm depends only on `(S, R, d)`.

**Step 4 (faithfulness).** Let `theta : G -> Aut(T_d)` be faithful and let
`g != 1`. Then `theta(g)` moves some vertex of some length `n`, so
`r_n o theta` is a homomorphism `G -> A_n` with `(r_n o theta)(g) != 1`. It is
determined by its values on `S`, which satisfy `R`, so it equals `rho_i` for
some `i`. Hence `rho_i(g)` moves some `u` with `|u| <= n_i`, and `tau(g)` moves
`1^i 0 u`. So `tau` is faithful.

**Consequence.** With `tau` faithful and computable, `g = 1` in `G` fails exactly
when some vertex is moved, which is a semi-decidable condition. Equality is
semi-decidable from the finite presentation. So the word problem is solvable.
The level-`n` quotient is `tau(G)` restricted to `X^{<=n}`, computed from
`tau(s)` for `s in S`. QED.
