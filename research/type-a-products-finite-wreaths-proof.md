---
rg: 2
id: type-a-products-finite-wreaths-proof
kind: route
title: Check the four type (A) clauses for the disjoint-union and imprimitive actions
target: type-a-actions-closed-under-products-and-finite-wreaths
requires: []
---

**Two remarks used below.**
- **Point orbits are finite in number.** If `|S| >= 2`, every point lies in a two-element subset, so each point orbit is hit by some orbit of two-element subsets. So there are finitely many point orbits. If `|S| = 1` there is one.
- **Ordered and unordered pairs give the same finiteness.** Finitely many orbits on unordered pairs, plus finitely many point orbits, give finitely many orbits on ordered pairs, and conversely.

**(a) Products.** `Gamma_1 x Gamma_2` acts on `S = S_1 ⊔ S_2` by
`(g_1, g_2) . s = g_i s` for `s` in `S_i`.
- *Faithful.* If `(g_1, g_2)` fixes every point, then `g_i` fixes `S_i`
  pointwise, so `g_i = 1` by faithfulness of each factor.
- *Finitely presented.* A product of two finitely presented groups is.
- *Stabilizers.* For `s` in `S_1`, the stabilizer is
  `Stab_(Gamma_1)(s) x Gamma_2`. It is finitely generated because both factors
  are. The case `s` in `S_2` is symmetric.
- *Pair orbits.* A two-element subset lies inside `S_1`, inside `S_2`, or meets
  both.
  - Inside `S_1`: the second factor acts trivially there, so its orbits are
    the `Gamma_1`-orbits, finitely many. Inside `S_2` is the same.
  - Meeting both: it is `{s, t}` with `s` in `S_1` and `t` in `S_2`, and
    `(g_1, g_2)` sends it to `{g_1 s, g_2 t}`. Its orbits correspond to pairs
    (point orbit of `Gamma_1`, point orbit of `Gamma_2`), finitely many by the
    first remark.

**(b) Finite wreaths.** `W = Gamma^k x| S_k` acts on `S x [k]` as displayed in
the claim. It is an action: both `(gamma, sigma)((delta, tau)(s, i))` and
`(gamma (sigma . delta), sigma tau)(s, i)` equal
`(gamma_(sigma tau (i)) delta_(tau(i)) s, sigma tau(i))`.
- *Faithful.* An element fixing every point fixes every block `S x {i}`, and
  the blocks are nonempty, so `sigma = 1`. Then each `gamma_i` fixes `S`
  pointwise, so `gamma_i = 1`.
- *Finitely presented.* `Gamma^k` is finitely presented and has index `k!` in
  `W`, and a group with a finitely presented subgroup of finite index is
  finitely presented.
- *Stabilizers.* The stabilizer of `(s, i)` consists of the `(gamma, sigma)`
  with `sigma(i) = i` and `gamma_i` in `Stab_Gamma(s)`. It contains
  `Stab_Gamma(s) x Gamma^(k-1)` with finite index, so it is finitely generated.
- *Pair orbits.* Let the subset be `{(s, i), (t, j)}`.
  - If `i = j`, then `s != t`. Some `sigma` moves block `i` to block `1`, so
    the orbit is determined by the `Gamma`-orbit of `{s, t}` in the first
    block. Finitely many.
  - If `i != j`, then `S_k` carries the unordered pair of blocks `{i, j}` to
    `{1, 2}`. Coordinates 1 and 2 of `gamma` then move the two points
    independently, so the orbit is determined by the unordered pair of point
    orbits. Finitely many.

Both actions are therefore of type (A). ∎
