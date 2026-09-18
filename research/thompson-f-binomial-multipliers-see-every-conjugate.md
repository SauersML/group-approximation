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
artifacts:
  - experiments/f-audit-lenses-2026-09-17/audit_ore.py
  - experiments/f-audit-lenses-2026-09-17/audit_ore.log
  - research/artifacts/audit-two-unrefereed-f-claims-2026-09-18.md
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

## Attempts

### 2026-09-18 — referee pass (agent `e2-w2-audit-f`, wave `swarm-0917`): SURVIVES

This node landed ESTABLISHED in the 2026-09-17 wave with its referee votes never cast. This is the
missing pass. Three lenses; full record in
`research/artifacts/audit-two-unrefereed-f-claims-2026-09-18.md`. The "unreviewed" parenthetical in
the header above is superseded by this entry. **Verdict: survives; status unchanged.**

- **Gaps.** Steps 0–6 of the route were re-derived independently and none failed. The four places
  where a slip would be invisible on a reading — the Laurent-divisibility form of the coset test and
  its negative-exponent consequence, the identity `eps_{t_0 x}(b v) = (beta v)(x)` of Step 2, the
  identity `eps_{w x}(y a) = (Y_D a)(x)` of Step 4, and the re-indexing by `phi^k` in Step 5 — were
  additionally re-derived numerically. `experiments/f-audit-lenses-2026-09-17/audit_ore.py`
  implements `F` exactly as PL homeomorphisms of `[0,1]` with dyadic breakpoints and power-of-two
  slopes (group equality is tuple equality, `K = Q`), takes `g = g_1 g_2` with bumps `(0,1/2)` and
  `(1/2,1)` and `lambda = 2`, and reports PASS on all seven checks, including a falsification search
  that generated 30 random pairs `(b, v)` with `v` in `K[<h>]` transverse to a conjugate `t_0^{-1}
  <g> t_0` with `t_0` in `supp b`: none landed in `J`, as item 1 forbids.
- **Hypotheses and citations.** The route quotes exactly one import, left-orderability of `F` so
  that `K[V]` is a domain, and uses nothing else from it; the coset test is re-proved in Step 0, so
  the route does not inherit the trust surface of
  `thompson-f-twisted-x0-binomial-is-ore-with-every-element-proof`. Cross-checked against four
  established neighbours with no contradiction: the closing Remark of
  `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals-proof` is recovered verbatim as
  `b = 1`, `V = Stab_F(z)`; in `thompson-f-binomials-meet-ideals-with-separated-conjugates` every
  conjugate lies in `V_Z` and so fixes `Z`, meeting the necessary condition of item 1; for
  `g = x_0` the obstruction is vacuous because `Fix(x_0) = {0,1}`, so there is no collision with
  `thompson-f-twisted-x0-binomial-is-ore-with-every-element`; and item 2(c) of
  `thompson-f-one-bump-binomials-have-common-multiples` asserts `P R ∩ c R != 0`, a different
  statement from item 2's `P ∉ J`.
- **Calibration.** On Thompson's `T` three steps die, and they are exactly the steps that carry the
  `F`-specific corollaries: `K[T]` is not a domain (torsion), `Fix(h^n) = Fix(h)` fails for an
  element of rotation number `1/2`, and Step 4's bump count needs torsion-freeness. On the positive
  monoid the proof dies at the first line of Step 0, which needs `g^{-1}` for the bijection
  `Z -> <g>w`. Items 1–3 use no property of the ambient `G` beyond the stated domain hypothesis, so
  they hold verbatim in `PL_+([0,1])` and in Cleary's `F_tau`; the claim is correctly scoped, since
  only the fixed-point and bump-count corollaries are stated for `G = F`.

Two defects found, neither refuting, neither touching a theorem item or the kill list:

1. **`supp g` means the moved set, not its closure.** A bump endpoint of `g` lies in the closure and
   is fixed, so item 1's "maps a point `z` into `supp g`" must be read as "maps `z` to a point moved
   by `g`". Step 6 uses it in that sense (`(p,q) \ {m} = supp g`), so no step breaks.
2. **"Equivalent" overstates item 3 by one direction.** Under *What survives*, the sentence that the
   "Opposite orientations" reduction "is equivalent, for `b` in `K[V]`, to zoom-orbit dependence"
   drops the restriction that item 3 carries: item 3 is an equivalence only for multipliers *inside*
   `K[<g> V]`, while the Ore condition allows `v` anywhere in `R`. The established direction is
   *zoom-orbit dependence ⟹ `(1 + lambda g) R ∩ b R != 0`*, which is the direction the decomposition
   needs; the converse is open. (Independently, the "Opposite orientations" reduction being referred
   to is an open attempt of `thompson-f-every-twisted-binomial-is-ore-with-every-element` with a
   recorded gap in its "factor out powers of `g_1` and `g_2`" step, see
   `notes/thompson-f-is-amenable-swarm-2026-09-16.md`.)
