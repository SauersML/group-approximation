---
rg: 2
id: thompson-f-binomial-multipliers-see-every-conjugate
kind: claim
title: A multiplier putting b v into (1 + lambda g) R must generate a group containing a nontrivial power of every conjugate of g by the reduced support of b, and transverse binomial factors can always be divided out
distinct_from:
  thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals: its closing Remark is the case b = 1, V = Stab_F(z) of item 1 here; this proves the obstruction for every b, every subgroup V and every right coset, and adds the saturation and shift-dependence items.
  thompson-f-binomials-meet-ideals-with-separated-conjugates: that constructs multipliers inside K[V_Z] when the conjugates are separated; item 1 here shows that multipliers in one coset of V_Z exist only if every conjugate fixes Z, so the nesting method reaches no further than pointwise stabilizers of common fixed points.
  thompson-f-ore-obstructions-must-see-finite-support: that rules out leading-term and division-ring certificates of a non-Ore pair; this is a necessary condition on any common multiple with a binomial side, on the amenable side of the problem.
  thompson-f-every-twisted-binomial-is-ore-with-every-element: that is the open statement; this proves no case of it and records which multiplier classes cannot prove it.
---

**ESTABLISHED** (elementary; unreviewed; no priority claimed). Composition is right to left.

**Setting.** `G` is a group, `K` a field, `R = K[G]`, `g` in `G` of infinite order,
`lambda` in `K^x`, `mu = -1/lambda` and `J = (1 + lambda g) R`. For a right coset `<g> w`
put `eps_w(y) = sum_n y(g^n w) mu^n`. By Step 1 of
`thompson-f-twisted-x0-binomial-is-ore-with-every-element-proof`, `y` lies in `J` iff
`eps_w(y) = 0` for every `w`. Call `b` *reduced* if `supp b` meets every right coset
`<g> w` at most once. Every `b` has a reduced `b°` with `b - b°` in `J`, and
`b v` is in `J` iff `b° v` is. So "`b R ∩ J ≠ 0`" depends only on `b°`, and if `b° = 0`
then `b` lies in `J`.

1. **Support theorem.** Let `b` be reduced and nonzero, `V <= G` with `K[V]` a domain,
   `s` in `G`, and `v ≠ 0` in `K[V] s` with `b v` in `J`. Then for every `t` in `supp b`,
   `V ∩ t^-1 <g> t ≠ 1`.
   - *Every multiplier.* Apply it to `V_v = <x y^-1 : x, y in supp v>` (so `v` is in
     `K[V_v] s` for any `s` in `supp v`). If `K[G]` is a domain and `b v` is a nonzero
     element of `J ∩ b R`, then `V_v` contains a nontrivial power of `t^-1 g t` for every
     `t` in `supp b°`.
   - *Fixed points, `G = F`.* A nontrivial power of `t^-1 g t` has the same fixed points
     as `t^-1 g t`. So `Fix(V_v) ⊆ ∩_(t in supp b°) Fix(t^-1 g t)`: the multiplier's
     support group can fix only points fixed by every conjugate. Equivalently, if some
     `t` in `supp b°` maps a point `z` into `supp g`, no nonzero multiplier with support
     in one right coset of `Stab_F(z)` exists.
   - *Families.* For `c_t = t^-1 g t` over a finite `T`, a nonzero `v` in
     `∩_(t in T) (1 + lambda c_t) R` satisfies `Fix(V_v) ⊆ ∩_t Fix(c_t)`.
2. **Transverse saturation.** Let `A <= G` meet every conjugate of `<g>` trivially, with
   `K[A]` a domain. If `y a` lies in `J` for some `y` in `R` and nonzero `a` in `K[A]`, then
   `y` lies in `J`.
   - So `J` contains no nonzero `u a_1 ... a_m` with `u` in `G` and each `a_i` a nonzero
     element of some `K[A_i]` as above.
   - In `F`: a nontrivial power of `h` is conjugate into `<g>` only if `h` and `g` have the
     same number of support components. If `g` has `k >= 2` bumps, `J` contains no unit
     times a product of twisted binomials `1 + mu_i h_i` of one-bump elements, and a
     multiplier `v = v' (1 + mu h)` with `h` one-bump can be replaced by `v'`.
3. **Shift dependence.** Let `V <= G` be normalized by `g`, with `V ∩ <g> = 1` and `K[V]` a
   domain, and let `b` be in `K[V]`. Put `phi(x) = g^-1 x g`. Then some nonzero `v` in
   `K[<g> V]` has `b v` in `J` iff some `r_0, ..., r_N` in `K[V]`, not all zero, have
   `sum_a phi^a(b) r_a = 0`.

**What this kills (for `thompson-f-every-twisted-binomial-is-ore-with-every-element`).**
- *Local nesting in any subgroup.* Every method whose common multiple lies in one right
  coset of a subgroup `V` needs `V` to contain nontrivial powers of all conjugates
  `t^-1 g t`, `t` in `supp b°`. It cannot pass to a group ring smaller than one containing
  those powers. This contains the dead "Local-to-global nesting through stabilizers".
- *Pointwise stabilizers.* A multiplier in one coset of `V_Z = Stab_F(Z)` exists only if
  every conjugate fixes `Z`. For conjugates whose supports cover every candidate separating
  point, no product-of-bump-groups nesting works.
- *Shift counts inside a fixed-point stabilizer.* Guba-type multipliers
  `v = sum_a g^a r_a` with every `r_a` supported in a monoid fixing a fixed point `z` of
  `g` (steps 5c–5g of `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals-proof`,
  the one-sided monoid `M`, and products `M × M` of the two sides of a shared endpoint)
  fail against every `b` with a monomial `t` of `b°` such that `t(z)` is in `supp g`.
  That is exactly the endpoint-moving case, so an extended count must use letters that
  move `z`.
- *Product-class reduction.* Showing that `J` contains an element of the one-bump product
  class of item 2(c) of `thompson-f-one-bump-binomials-have-common-multiples` cannot work
  for multi-bump `g`.

**What survives, as a precise decomposition.** By item 3 with
`V = <g_1> ⋉ F_c(p,q)` (the compactly supported elements of `F_(p,q)`, extended by the
first bump), the "Opposite orientations" reduction for `g = g_1 g_2` with bumps `(p,m)`
and `(m,q)` is equivalent, for `b` in `K[V]`, to *zoom-orbit dependence*: the conjugates
`g^-a b g^a`, `a = 0..N`, are right linearly dependent over `K[V]` for some `N`. By item 1,
the coefficients `r_a` must have support groups moving `m` whenever `b` has a monomial
moving `m`. For one bump (`g = x_0`, `V` = elements trivial near `0`) this dependence is
Steps 4–5 of the twisted-`x_0` route.

Proof route: `thompson-f-binomial-multipliers-see-every-conjugate-proof`.
