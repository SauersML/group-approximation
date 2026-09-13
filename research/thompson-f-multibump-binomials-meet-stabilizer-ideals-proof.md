---
rg: 2
id: thompson-f-multibump-binomials-meet-stabilizer-ideals-proof
kind: route
title: Adjoin the other bumps as central variables, apply the one-bump theorem over the rational function field in them, restrict to H_i and clear central denominators
target: thompson-f-multibump-binomials-meet-stabilizer-ideals
requires: [thompson-f-one-bump-binomials-have-common-multiples]
---

Notation as in the target.

**Step 1 (the subgroups).**
- *Commuting.* Let `h` be in `H_i` and `j ≠ i`. `h` fixes `[p_j, q_j]` pointwise, so it
  maps the complement onto itself.
  - On `[p_j, q_j]`, `g_j` preserves the interval, so `h g_j = g_j = g_j h` there.
  - Off it, `g_j` is the identity and `h` keeps points off it, so `h g_j = h = g_j h`.
- *Trivial intersection and rank.* Let `z = prod_(j ≠ i) g_j^(a_j)`. On `(p_j, q_j)`, `z`
  acts as `g_j^(a_j)`, which is nontrivial when `a_j ≠ 0`. Elements of `H_i` are the
  identity there. So `z` lies in `H_i` only when every `a_j = 0`, and `Z_i ≅ Z^(k-1)`.
- *Membership.* `g_i` is the identity outside `(p_i, q_i)`, which misses every closed
  interval `[p_j, q_j]` with `j ≠ i`.
- Commuting subgroups with trivial intersection generate their direct product.

**Step 2 (central variables).** Let `L = K(z_j : j ≠ i)` be the rational function field
in `k - 1` variables.
- The map `iota : K[H_i × Z_i] -> L[H_i]`, `h prod_j g_j^(a_j) -> (prod_j z_j^(a_j)) h`, is
  a ring homomorphism because `Z_i` is central in `H_i × Z_i` and the `z_j` are central in
  `L[H_i]`.
- `iota` is injective: it is the tensor product over `K` of the identity of `K[H_i]` with
  the inclusion `K[z_j^{+-1}] ⊆ L`, and tensoring over a field preserves injectivity.
- `iota(1 + lambda g) = 1 + mu g_i` with `mu = lambda prod_(j ≠ i) z_j` in `L^x`. Put
  `beta = iota(b) ≠ 0`.

**Step 3 (one bump over `L`).** `g_i` is one-bump, and
`thompson-f-one-bump-binomials-have-common-multiples` holds over every field. Item 2(b)
over `L` gives `(1 + mu g_i) u = beta v ≠ 0` for some `u, v` in `L[F]`.
- *Restriction.* Choose representatives `S` of the right cosets `H_i s`. As left
  `L[H_i]`-modules, `L[F] = ⊕_(s in S) L[H_i] s`.
- Write `u = sum_s u_s s` and `v = sum_s v_s s` with `u_s, v_s` in `L[H_i]`. Since
  `1 + mu g_i` and `beta` lie in `L[H_i]`, uniqueness of components gives
  `(1 + mu g_i) u_s = beta v_s` for every `s`, and some component is nonzero.
- So there are `u', v'` in `L[H_i]` with `(1 + mu g_i) u' = beta v' ≠ 0`.

**Step 4 (clearing denominators).**
- The finitely many coefficients of `u'` and `v'` lie in `L`. Choose a nonzero polynomial
  `d` in `K[z_j : j ≠ i]` such that `d u'` and `d v'` have coefficients in
  `K[z_j^{+-1}]`, that is, lie in the image of `iota`.
- `d` is central in `L[H_i]`, so `(1 + mu g_i)(d u') = d beta v' = beta (d v')`. This is
  nonzero because `d` is a unit of `L`.
- Let `u''` and `v''` be the preimages under `iota`. Injectivity gives
  `(1 + lambda g) u'' = b v'' ≠ 0` in `K[H_i × Z_i]`, a subring of `R`.
- So `(1 + lambda g) R ∩ b R ≠ 0`. For `b s` with `s` in `F`, `b s R = b R`.

**Trust surfaces.**
- Quoted: `thompson-f-one-bump-binomials-have-common-multiples`, used over the field `L`.
  Its statement is for an arbitrary field `K`.
- Everything else is proved above.
