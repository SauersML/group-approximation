---
rg: 2
id: thompson-f-binomial-multipliers-see-every-conjugate-proof
kind: route
title: Split the induced module R/(1 + lambda g)R over the double cosets <g> w V; on a free double coset the coset test turns b v into beta v for a nonzero beta in the domain K[V]
target: thompson-f-binomial-multipliers-see-every-conjugate
requires: []
---

Notation as in the target. Composition is right to left. For `y` in `R` and `h` in `G`,
`y(h)` is the coefficient of `h`. The only outside input is that `K[F]` is a domain because
`F` is left-orderable (derivation step 2 of `thompson-f-amenable-iff-group-ring-is-ore`),
so `K[V]` is a domain for every `V <= F`.

**Step 0 (coset test, re-proved for any `g` of infinite order).** `1 + lambda g =
lambda (g - mu)`, so `J = (g - mu) R`.
- Fix a right coset `C = <g> w`. Since `g` has infinite order, `n -> g^n w` is a bijection
  `Z -> C`. For `y` in `R` put `Y_C(t) = sum_n y(g^n w) t^n` in `K[t, t^-1]`. The
  coefficient of `(g - mu) u` at `g^n w` is `u(g^(n-1) w) - mu u(g^n w)`, so the restriction
  of `(g - mu) u` to `C` is `(t - mu) U_C(t)`. Every element of `R` splits over the finitely
  many cosets it meets, and `u` can be chosen coset by coset. So `y` lies in `J` iff every
  `Y_C` is divisible by `t - mu`, that is, iff `eps_w(y) = Y_C(mu) = 0` for every `w`.
- `eps_(g w) = mu^-1 eps_w`, so the condition does not depend on the representative.
- *Consequence.* `g^a y - mu^a y` lies in `J` for all `y` and all integers `a`: for `a >= 0`
  `g^a - mu^a` is a left multiple of `g - mu` in the commutative ring `K[<g>]`, and for
  `a < 0`, `g^a - mu^a = -mu^a g^a (g^(-a) - mu^(-a))`.

**Step 1 (reduction to reduced `b`).** Group the monomials of `b` by right coset. In a coset
`<g> w`, replace `b(g^n w) g^n w` by `b(g^n w) mu^n w`. By Step 0 each replacement changes
`b` by an element of `J`. The result `b°` is reduced, and `b - b°` lies in `J`. Since `J` is
a right ideal, `b v - b° v = (b - b°) v` lies in `J`, so `b v` is in `J` iff `b° v` is.

**Step 2 (item 1, support theorem).** Let `b`, `V`, `s`, `v` be as in item 1.
- *`s = 1`.* `J s^-1 = J`, `b (v s^-1)` lies in `J`, and `v s^-1` is a nonzero element of
  `K[V]`.
- Suppose some `t_0` in `supp b` has `V ∩ t_0^-1 <g> t_0 = 1`, and let `D = <g> t_0 V`.
- *Normal form on `D`.* Every element of `D` is `g^m t_0 c` with `m` in `Z`, `c` in `V`, and
  this is unique: `g^m t_0 c = g^(m') t_0 c'` gives `t_0^-1 g^(m-m') t_0 = c' c^-1`, which
  lies in `V ∩ t_0^-1 <g> t_0 = 1`. So `g^(m-m') = 1`, hence `m = m'` and `c = c'`.
- *The coefficient `beta`.* Let `T_D = supp b ∩ D`, which contains `t_0`, and write
  `t = g^(m_t) t_0 c_t`. If `c_t = c_(t')` then `t` and `t'` lie in the same right coset
  `<g> t_0 c_t`, so `t = t'` because `b` is reduced. The `c_t` are distinct, so
  `beta = sum_(t in T_D) b(t) mu^(m_t) c_t` is a nonzero element of `K[V]`.
- *Coset values.* Fix `x` in `V`. Then `(b v)(h) = sum b(t) v(y)` over pairs
  `(t, y)` in `supp b × V` with `t y = h`. If `t y` lies in `<g> t_0 x`, then `t` lies in
  `<g> t_0 x y^-1 ⊆ D`, so `t` is in `T_D`, and `t y = g^(m_t) t_0 c_t y`. This lies in
  `<g> t_0 x` iff `t_0 c_t y x^-1 t_0^-1` is in `<g>`, i.e. iff `c_t y x^-1` lies in
  `V ∩ t_0^-1 <g> t_0 = 1`. So `y = c_t^-1 x` and `t y = g^(m_t) t_0 x`. Hence
  `eps_(t_0 x)(b v) = sum_(t in T_D) b(t) mu^(m_t) v(c_t^-1 x) = (beta v)(x)`.
- *Conclusion.* If `b v` is in `J`, Step 0 gives `(beta v)(x) = 0` for every `x` in `V`, so
  `beta v = 0`. Since `K[V]` is a domain and `beta ≠ 0`, `v = 0`. That is a contradiction,
  so `V ∩ t^-1 <g> t ≠ 1` for every `t` in `supp b`.

**Step 3 (item 1, corollaries).**
- *Every multiplier.* Let `b v` be a nonzero element of `J ∩ b R`, so `v ≠ 0`, and let `s`
  be in `supp v`. Every `x` in `supp v` is `(x s^-1) s` with `x s^-1` in `V_v`, so `v` lies in
  `K[V_v] s`. `K[V_v]` is a domain because `K[G]` is. By Step 1, `b° v` lies in `J`. If
  `b° ≠ 0`, Step 2 applies to `b°`, `V_v`, `s`, `v`. If `b° = 0` the statement is empty.
- *Fixed points in `F`.* An increasing homeomorphism of `[0,1]` with a periodic point fixes
  it, so `Fix(h^n) = Fix(h)` for `n ≠ 0`. By Step 2, `V_v` contains `t^-1 g^n t` for some
  `n ≠ 0`, whose fixed-point set is `t^-1 Fix(g^n) = t^-1 Fix(g) = Fix(t^-1 g t)`. A point
  fixed by `V_v` is fixed by this element, so `Fix(V_v) ⊆ Fix(t^-1 g t)` for every `t` in
  `supp b°`.
- *Right cosets of `Stab_F(z)`.* If `supp v ⊆ Stab_F(z) s`, then `x y^-1` lies in
  `Stab_F(z)` for all `x, y` in `supp v`, so `z` is in `Fix(V_v)` and hence `t(z)` is in
  `Fix(g)` for every `t` in `supp b°`. So a `t` with `t(z)` in `supp g` rules out every such
  `v`.
- *Families.* Let `c_t ≠ 1` in `F` over a finite `T`, and let `v ≠ 0` lie in every
  `(1 + lambda c_t) R`. Apply Step 2 with `g` replaced by `c_t`, `b = 1` (reduced),
  `V = V_v`, and `t_0 = 1`. It gives `V_v ∩ <c_t> ≠ 1`, and as above
  `Fix(V_v) ⊆ Fix(c_t)`.

**Step 4 (item 2, transverse saturation).** Let `A`, `y`, `a` be as in item 2.
- *Free double cosets.* Fix a double coset `D = <g> w A` with a chosen representative `w`.
  As in Step 2, `A ∩ w^-1 <g> w = 1` makes `x -> <g> w x` injective on `A`. So the function
  `Y_D(x) = eps_(w x)(y)` on `A` is nonzero only at the finitely many `x` whose coset meets
  `supp y`, and `Y_D` is an element of `K[A]`.
- *Coset values.* `(y a)(h) = sum_(z in A) y(h z^-1) a(z)`, so
  `eps_(w x)(y a) = sum_z a(z) sum_n mu^n y(g^n w x z^-1) = sum_z Y_D(x z^-1) a(z) = (Y_D a)(x)`.
- *Conclusion.* If `y a` lies in `J`, every `Y_D a` is `0`, so every `Y_D` is `0` because
  `K[A]` is a domain. Every `w'` in `G` lies in some `D`, as `w' = g^m w x`, and
  `eps_(w')(y) = mu^-m Y_D(x) = 0`. By Step 0, `y` lies in `J`.
- Without freeness the argument fails, and it must: for `A = <g>`, `(1 + lambda g)` is in `J`
  and `1` is not. There `x -> eps_(w x)(y)` is not finitely supported.
- *Products.* `J ≠ R`, since `eps_1(1) = 1`. If `u a_1 ... a_m` is in `J`, peeling off
  `a_m, ..., a_1` by the main statement puts the unit `u` in `J`, which is impossible.
- *Bump counts in `F`.* For `h ≠ 1`, `supp h^n = supp h` for `n ≠ 0` (fixed points as in
  Step 3), and conjugation by a homeomorphism preserves the number of components of the
  support. If `h^n = w^-1 g^m w` with `n ≠ 0`, then `m ≠ 0` because `F` is torsion-free, so
  `h` and `g` have the same number of bumps. So if `h` is one-bump and `g` has `k >= 2` bumps,
  `A = <h>` meets every conjugate of `<g>` trivially. `K[<h>]` is a domain, and `1 + mu h ≠ 0`.
  That gives both consequences stated in item 2: no unit times such a product lies in `J`, and
  `b v' (1 + mu h)` in `J` forces `b v'` in `J`.

**Step 5 (item 3, shift dependence).** Let `V`, `g`, `b`, `phi` be as in item 3.
- *Normal forms.* `g^-1 V g = V`, so `phi` is an automorphism of `V` and of `K[V]`, and
  `<g> V` is a subgroup. Its elements are uniquely `g^a x` with `a` in `Z`, `x` in `V`, since
  `V ∩ <g> = 1`. Also `b g^a = g^a phi^a(b)`.
- *Congruence.* Write `v = sum_a g^a r_a` with `r_a` in `K[V]`. Then
  `b v = sum_a g^a phi^a(b) r_a`, which by Step 0 is congruent modulo `J` to
  `z = sum_a mu^a phi^a(b) r_a` in `K[V]`.
- *`K[V] ∩ J = 0`.* For `x ≠ x'` in `V` the cosets `<g> x` and `<g> x'` differ, and `<g> x`
  meets `V` only in `x`. So for `z` in `K[V]`, `eps_x(z) = z(x)`, and `z` is in `J` iff
  `z = 0`. Thus `b v` is in `J` iff `sum_a mu^a phi^a(b) r_a = 0`.
- *Only if.* Given `v ≠ 0` with indices `a` in `[-k, N - k]`, apply the automorphism
  `phi^k` and put `r'_(a+k) = mu^a phi^k(r_a)`. Then `sum_(a'=0)^N phi^(a')(b) r'_(a') = 0`,
  and not all `r'` are zero.
- *If.* Given `r_0, ..., r_N`, not all zero, with `sum_a phi^a(b) r_a = 0`, put
  `v = sum_a mu^-a g^a r_a`. It is nonzero by uniqueness of normal forms, and
  `sum_a mu^a phi^a(b) mu^-a r_a = 0`.

**Step 6 (checks on the kill list).**
- *Endpoint Remark.* `b = 1`, `V = Stab_F(z)` and `c` moving `z` is Step 3 applied to right
  cosets. The Remark of `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals-proof`
  says the same thing.
- *Separated conjugates.* There every conjugate lies in `V_Z`, so it fixes `Z`, as Step 3
  requires. No inconsistency.
- *Shift counts.* If every `r_a` is supported in `Stab_F(z)` with `g(z) = z`, then
  `supp (sum_a mu^-a g^a r_a) ⊆ Stab_F(z)`. By Step 3 no such multiplier works against a `b`
  with a monomial `t` of `b°` such that `t(z)` is in `supp g`. With a left prefactor `u` (as in
  5c–5d, where the multiplier is `c^(K_0) s w'`), the support lies in the left coset
  `u Stab_F(z)`. Then `V_v ⊆ u Stab_F(z) u^-1 = Stab_F(u(z))`, and the same obstruction holds
  with `u(z)` in place of `z`.
- *Surviving decomposition.* For `g = g_1 g_2` with bumps `(p, m)` and `(m, q)`, the group
  `V = <g_1> F_c(p,q)` satisfies item 3:
  - `g` normalizes `F_c(p,q)`, and `g^-1 g_1 g = g_1` because `g_2` commutes with `g_1`;
  - `V ∩ <g> = 1`, since near `q`, `g^n = g_2^n` while elements of `V` are the identity there.
  Every `b` in `K[V]` is reduced, because `<g> x` meets `V` only in `x`. If every `r_a` lies in
  `K[Stab_V(m)]`, the multiplier lies in `Stab_F(m)`. Every `t` in `V` with `t(m) ≠ m` has
  `t(m)` in `(p,q) \ {m} = supp g`, so Step 3 excludes these multipliers as soon as `b` has a
  monomial moving `m`.

**Trust surfaces.** Quoted: left-orderability of `F`, so that its subgroup rings are domains.
Everything else, including the coset test, is proved above.
