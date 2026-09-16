---
rg: 2
id: support-minimal-zero-divisor-no-up-quotient-proof
kind: route
title: Split a minimal zero divisor along cosets and along a unique-product quotient; minimality forbids both splittings
target: support-minimal-zero-divisor-groups-have-no-up-quotient
requires: []
---

Notation as in the target. Write `|gamma|` for `|supp gamma|`.

**Step 0 (translation).** For `g, h in G`, `(g^-1 alpha)(beta h^-1) =
g^-1 (alpha beta) h^-1 = 0`, and the support sizes are unchanged. So the
translated pair is again support-minimal. Fix `g in supp alpha` and
`h in supp beta`, and rename the translated pair `(alpha, beta)`. Now
`1 in supp alpha ∩ supp beta`.

For a finite set `X` and `g in X`, `<g^-1 X> = <x^-1 y : x, y in X>`. Indeed
`g^-1 x` has this form, and `x^-1 y = (g^-1 x)^-1 (g^-1 y)`. Likewise
`<X h^-1> = <x y^-1 : x, y in X>`. So the groups named in item 1 do not depend
on the translation.

**Step 1 (both supports generate the same group).** Put `L = <supp alpha>`
and `M = <supp beta>`.
- For each right coset `Lx`, let `beta_{Lx}` be the restriction of `beta` to
  `Lx`. Then `alpha beta_{Lx}` is supported in `L · Lx = Lx`. Distinct cosets
  are disjoint, so `alpha beta = 0` forces `alpha beta_{Lx} = 0` for every
  coset.
- Pick a coset with `beta_{Lx} != 0`. Minimality gives
  `|beta_{Lx}| >= |beta|`, so `supp beta ⊆ Lx`. Since `1 in supp beta`,
  `Lx = L`. Hence `M <= L`.
- Symmetrically, for each left coset `yM`, let `alpha_{yM}` be the
  restriction of `alpha` to `yM`. Then `alpha_{yM} beta` is supported in
  `yM · M = yM`, so each of these products is zero. Pick a coset with
  `alpha_{yM} != 0`. Minimality gives `supp alpha ⊆ yM`, and since
  `1 in supp alpha`, `yM = M`. Hence `L <= M`.

Hence `L = M = H`, which is item 1.

`H != 1`: otherwise `alpha` and `beta` are nonzero scalars, and their product
is nonzero.

**Step 2 (unique-product quotients).** Let `phi : H -> Q'` be a homomorphism
to a unique-product group. Put `Q = phi(H)`, which has unique products as a
subgroup of `Q'`, and `N = ker phi`.
- Choose a transversal `q -> t_q in H` of `N` with `t_1 = 1`. Then
  `k[H] = ⊕_{q in Q} k[N] t_q`.
- Write `alpha = sum_p alpha_p t_p` and `beta = sum_q beta_q t_q` with
  `alpha_p, beta_q in k[N]`. Here `alpha_p t_p` is the restriction of `alpha`
  to the coset `N t_p`, so `|alpha_p| = |supp alpha ∩ N t_p|`, and
  `alpha_p != 0` iff `p in A := phi(supp alpha)`. The same holds for `beta`,
  with `B := phi(supp beta)`.
- With `t_p t_q = tau(p, q) t_{pq}`, where `tau(p, q) in N`,

```text
alpha beta = sum_{p in A, q in B} alpha_p (t_p beta_q t_p^-1) tau(p, q) t_{pq},
```

  and each summand lies in `k[N] t_{pq}`.
- Since `Q` has unique products, some `r_0 in AB` has a unique expression
  `r_0 = p_0 q_0` with `p_0 in A` and `q_0 in B`. The `k[N] t_{r_0}`-component
  of `alpha beta` is `alpha_{p_0} beta' tau(p_0, q_0)`, where
  `beta' = t_{p_0} beta_{q_0} t_{p_0}^-1`. It vanishes, and `tau(p_0, q_0)` is
  a unit, so `alpha_{p_0} beta' = 0`.
- Both `alpha_{p_0}` and `beta'` are nonzero, with `|alpha_{p_0}| <= |alpha|`
  and `|beta'| = |beta_{q_0}| <= |beta|`. By minimality both are equalities.
  So `supp alpha ⊆ N t_{p_0}` and `supp beta ⊆ N t_{q_0}`.
- Since `1 in supp alpha`, `N t_{p_0} = N`, so `supp alpha ⊆ N`. Then
  `H = <supp alpha> <= N`, and `phi` is trivial. This is item 2.

**Step 3 (consequences).**
- *Left-orderable groups have unique products.* In a left-ordered group, let
  `X` and `Y` be finite nonempty and `m = max XY`. If `m = xy` with
  `y < max Y`, then `xy < x max Y <= m`, which is impossible. So `y = max Y`
  and `x = m (max Y)^-1`, and `m` has a unique expression. Hence item 2 kills
  every homomorphism to a left-orderable group, in particular to `Z` with its
  usual order.
- *Free groups.* A nontrivial homomorphism to a free group has a nontrivial,
  finitely generated, free image, which maps onto `Z`. So it is excluded.
- *Abelianization.* `H` is finitely generated, since `supp alpha` is finite.
  So `H^ab` is a finitely generated abelian group with no quotient `Z`, and it
  is finite.
- *Unique products.* The identity map of `H` is nontrivial, so `H` does not
  have unique products.
- *Local indicability.* `H` is itself a nontrivial finitely generated subgroup
  with no quotient `Z`, so `H` is not locally indicable.

**The reduction.** Let `G` be torsion-free with a zero divisor over `k`. A
support-minimal pair exists, since support sizes are positive integers. Its
group `H` is a subgroup of `G`, hence torsion-free. Both supports lie in `H`,
so the pair is a zero divisor in `k[H]`. The converse direction is trivial. □
