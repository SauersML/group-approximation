---
rg: 2
id: thompson-f-binomials-meet-ideals-with-separated-conjugates-proof
kind: route
title: Spanning products have property O by the bump-endpoint claim; nest by hulls one endpoint coordinate at a time, conjugating by the running multiple to freeze the coordinate being released
target: thompson-f-binomials-meet-ideals-with-separated-conjugates
requires: [thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals]
---

Notation as in the target. Composition is right to left. A one-bump element is an element
of `F` whose support is a single open interval.

**Preliminaries.**
- *(D) Domains.* `F` is left-orderable, so `K[H]` is a domain for every subgroup `H`.
- *(E) Endpoints.* Let `c` in `F` fix a point `e` and move every point of `(e - eps, e)`
  but none of `(e, e + eps)`, or the reverse. Near `e` on the moving side, `c` is affine,
  fixes `e`, and has slope `≠ 1`, because an affine map fixing `e` with slope `1` is the
  identity. So `e` is a breakpoint of `c`, or `e` is `0` or `1`, and in each case `e` is
  dyadic. In particular the endpoints of a one-bump element are dyadic, and so is an endpoint
  `q_i < p_(i+1)` of a gap between consecutive bumps.
- *(V) Products.* For dyadic `u < v`, `F_[u,v]` is the group of elements of `F` supported in
  `[u, v]`. For dyadic `Z`, an element fixing every `z_i` restricts on each
  `[z_(i-1), z_i]` to an element `c_i` of `F_[z_(i-1),z_i]`, and any tuple of such elements
  glues to an element of `F` because the `z_i` are dyadic. So `V_Z = prod_i F_[z_(i-1),z_i]`
  and `c = c_1 ... c_k` uniquely.

**Lemma A (restriction).** Let `H <= H' <= F` and `a, y` in `K[H]`. If
`a K[H'] ∩ y K[H'] ≠ 0`, then `a K[H] ∩ y K[H] ≠ 0`.
- Choose representatives `S` of the right cosets `H s` in `H'`. As a left `K[H]`-module,
  `K[H'] = ⊕_(s in S) K[H] s`.
- If `a u = y v ≠ 0` with `u = sum_s u_s s` and `v = sum_s v_s s`, then `a u_s = y v_s` for
  every `s`. Some `u_s ≠ 0`, and then `a u_s ≠ 0` by (D).

**Lemma B (conjugates absorb).** Let `G <= F`, `c` in `G`, `lambda` in `K^x`, and `y` in
`K[G]`. If `v` lies in `(1 + lambda t^-1 c t) K[G]` for every `t` in `supp y`, then `y v`
lies in `(1 + lambda c) K[G]`.
- Write `v = (1 + lambda t^-1 c t) u_t` with `u_t` in `K[G]`. Since
  `t (1 + lambda t^-1 c t) = (1 + lambda c) t` and `t` lies in `G`, `t v = (1 + lambda c) t u_t`
  lies in `(1 + lambda c) K[G]`.
- `y v = sum_t y(t) t v`.

**Shape and hull.** Fix dyadic `Z = {z_1 < ... < z_(k-1)}`, with `z_0 = 0` and `z_k = 1`.
- *Shape.* For Z-one-bump `c = c_1 ... c_k`, write `supp c_l = (a_l(c), d_l(c))`, so
  `z_(l-1) <= a_l(c) < d_l(c) <= z_l`. The *shape coordinates* of `c` are
  `a_1, d_1, a_2, d_2, ..., a_k, d_k`: coordinate `2l - 1` is `a_l(c)` and coordinate `2l`
  is `d_l(c)`. All of them are dyadic by (E).
- *Hull.* For a finite nonempty family `𝔉` of Z-one-bump elements put
  `A_l = min_(c in 𝔉) a_l(c)`, `D_l = max_(c in 𝔉) d_l(c)`, and
  `H(𝔉) = F_[A_1,D_1] ... F_[A_k,D_k]`.
  - Since `z_(l-1) <= A_l < D_l <= z_l`, the open intervals `(A_l, D_l)` are pairwise
    disjoint. So the factors commute, `H(𝔉) <= V_Z`, and every `t` in `H(𝔉)` is a product
    `t_1 ... t_k` with `t_l` in `F_[A_l,D_l]`, acting on `[z_(l-1), z_l]` as `t_l`.
  - Every `c` in `𝔉` lies in `H(𝔉)`, because `c_l` lies in
    `F_[a_l(c),d_l(c)] <= F_[A_l,D_l]`.
- *Conjugates.* For Z-one-bump `c` and `t` in `V_Z`, `t^-1 c t` lies in `V_Z`, and its
  restriction to `[z_(l-1), z_l]` is `t_l^-1 c_l t_l`, with support
  `(t^-1(a_l(c)), t^-1(d_l(c)))`. So `t^-1 c t` is Z-one-bump, and its shape coordinates
  are the images under `t^-1` of those of `c`.

**Lemma 2 (fixed shape).** Let `c` be Z-one-bump with shape `(a_l, d_l)`, and put
`L = F_[a_1,d_1] ... F_[a_k,d_k]`. For every `lambda` in `K^x` and every nonzero `y` in
`K[L]`, `(1 + lambda c) K[L] ∩ y K[L] ≠ 0`.
- `c ≠ 1`, and the support of `c` is the union of the pairwise disjoint open intervals
  `(a_l, d_l)`. They are distinct components even when `d_l = z_l = a_(l+1)`, because `c`
  fixes that point. Their endpoints are dyadic by (E).
- So `c` satisfies the hypothesis of
  `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals`, with
  `∂_c = {a_1, d_1, ..., a_k, d_k}`.
- An element of `F_[a_l,d_l]` fixes every point outside `(a_l, d_l)`, and in particular
  every point of `∂_c`. So `L <= W_c`, and `y` is a nonzero element of `K[W_c]`.
- Item 1 of that claim gives `(1 + lambda c) R ∩ y R ≠ 0`. Both `1 + lambda c` and `y` lie
  in `K[L]`, so Lemma A with `H = L` and `H' = F` gives the statement.

**Proposition T(m), for `0 <= m <= 2k`.** Let `𝔉 = (c^(1), ..., c^(r))`, `r >= 1`, be
Z-one-bump elements that agree in the shape coordinates with indices `m + 1, ..., 2k`, and
let `lambda_1, ..., lambda_r` be in `K^x`. Then there is a nonzero `w` in `K[H(𝔉)]` that
lies in `(1 + lambda_j c^(j)) K[H(𝔉)]` for every `j`.

*T(0).* All members have the same shape `(a_l, d_l)`, so `H(𝔉) = L` as in Lemma 2.
- Put `w_1 = 1 + lambda_1 c^(1)`, which is nonzero because `c^(1) ≠ 1`.
- Given a nonzero `w_j` in `K[L]` lying in `(1 + lambda_i c^(i)) K[L]` for all `i <= j`,
  Lemma 2 gives `u, u'` in `K[L]` with `w_j u = (1 + lambda_(j+1) c^(j+1)) u' ≠ 0`.
- Put `w_(j+1) = w_j u`. It lies in the earlier ideals because they are right ideals.
- `w = w_r` is the required element.

*From T(m - 1) to T(m), `m >= 1`.* Let `𝔉` agree in coordinates `m + 1, ..., 2k`.
Coordinate `m` is `d_i` if `m = 2i`, and `a_i` if `m = 2i - 1`.
- *Ordering.* If `m = 2i`, order the members so that `d_i(c^(1)) <= ... <= d_i(c^(r))`. If
  `m = 2i - 1`, order them so that `a_i(c^(1)) >= ... >= a_i(c^(r))`.
- *Notation.* `H_j = H(c^(1), ..., c^(j))`, with interval endpoints `A_l^j` and `D_l^j`. So
  `A_l^(j+1) <= A_l^j < D_l^j <= D_l^(j+1)`, `H_j <= H_(j+1)` and `H_r = H(𝔉)`.

*Claim.* For every `j` there is a nonzero `w_j` in `K[H_j]` lying in
`(1 + lambda_i c^(i)) K[H_j]` for every `i <= j`.
- *`j = 1`.* Take `w_1 = 1 + lambda_1 c^(1)`.
- *From `j` to `j + 1`.* Put `c = c^(j+1)`, `lambda = lambda_(j+1)`, `T = supp w_j`, which
  is nonempty and lies in `H_j`, and `c_t = t^-1 c t` for `t` in `T`.

*(i) The conjugates.* Each `t` in `T` lies in `H_j <= V_Z`, so `c_t` is Z-one-bump and its
shape coordinates are the images of those of `c` under `t^-1` ("Conjugates" above).

*(ii) Coordinates `m, ..., 2k` are frozen.* Every `t` in `T` fixes the shape coordinates of
`c` with index at least `m`. Write `t = t_1 ... t_k` with `t_l` in `F_[A_l^j,D_l^j]`; then
`t_l` fixes `A_l^j`, `D_l^j` and every point of `[z_(l-1), z_l]` outside
`(A_l^j, D_l^j)`.
- *Index `> m`.* All members agree there. For coordinate `a_l` this gives
  `A_l^j = a_l(c)`, and for coordinate `d_l` it gives `D_l^j = d_l(c)`. These are
  endpoints fixed by `t_l`.
- *Index `m = 2i`.* By the ordering, `D_i^j = max_(i' <= j) d_i(c^(i')) <= d_i(c)`, and
  `d_i(c) <= z_i`. So `d_i(c)` lies in `[D_i^j, z_i]`, which `t_i` fixes pointwise.
- *Index `m = 2i - 1`.* By the ordering, `A_i^j >= a_i(c)`, and `a_i(c) >= z_(i-1)`. So
  `a_i(c)` lies in `[z_(i-1), A_i^j]`, which `t_i` fixes pointwise.
- Consequently all `c_t` with `t` in `T` agree in coordinates `m, ..., 2k`, with the values
  of `c`.

*(iii) Apply T(m - 1).* Let `𝔉'` be the family `(c_t)_(t in T)`, all with the scalar
`lambda`. By (ii) it agrees in coordinates `(m - 1) + 1, ..., 2k`. T(m - 1) gives a
nonzero `v` in `K[H(𝔉')]` lying in `(1 + lambda c_t) K[H(𝔉')]` for every `t` in `T`.

*(iv) Containment of hulls.* `H(𝔉') <= H_(j+1)`.
- `t_l` is supported in `[A_l^j, D_l^j] ⊆ [A_l^(j+1), D_l^(j+1)]`, so `t_l` and `t_l^-1` map
  `[A_l^(j+1), D_l^(j+1)]` onto itself.
- `a_l(c)` and `d_l(c)` lie in `[A_l^(j+1), D_l^(j+1)]`, because `c` is a member of the
  first `j + 1`.
- So `A_l^(j+1) <= t^-1(a_l(c))` and `t^-1(d_l(c)) <= D_l^(j+1)` for every `t` and `l`.
  Taking the minimum and maximum over `t` gives
  `F_[A_l(𝔉'),D_l(𝔉')] <= F_[A_l^(j+1),D_l^(j+1)]` for every `l`.

*(v) The next multiple.* Put `w_(j+1) = w_j v`.
- It is nonzero by (D), and it lies in `K[H_(j+1)]` because `w_j` lies in `K[H_j]` and
  `v` lies in `K[H(𝔉')]`, both inside `K[H_(j+1)]` by (iv).
- For `i <= j`, `w_j = (1 + lambda_i c^(i)) u_i` with `u_i` in `K[H_j]`. So
  `w_(j+1) = (1 + lambda_i c^(i)) u_i v` lies in `(1 + lambda_i c^(i)) K[H_(j+1)]`.
- For `i = j + 1`, apply Lemma B with `G = H_(j+1)`, the element `c` of `G`, and
  `y = w_j`. Its hypothesis holds by (iii) and (iv), since
  `(1 + lambda c_t) K[H(𝔉')] ⊆ (1 + lambda c_t) K[H_(j+1)]`. So `w_(j+1)` lies in
  `(1 + lambda c) K[H_(j+1)]`.

With `j = r` the claim gives T(m), because `H_r = H(𝔉)`.

**Item 1.** Apply T(2k), which requires no agreement, to `(c^(1), ..., c^(r))`. The
element `w` is nonzero and lies in every `(1 + lambda_j c^(j)) K[H(𝔉)]`, which is inside
`(1 + lambda_j c^(j)) K[V_Z]` and `(1 + lambda_j c^(j)) R`.

**Item 2.** Let `T = supp b`, `g`-separated by `Z`, and `c_t = t^-1 g t` for `t` in `T`.
- `supp c_t = t^-1(supp g)` is the union of the intervals `t^-1(I_i) ⊆ (z_(i-1), z_i)`. So
  `c_t` fixes every `z_i` and lies in `V_Z`. Its restriction to `[z_(i-1), z_i]` has support
  `t^-1(I_i)`, a single open interval, so `c_t` is Z-one-bump.
- Item 1 gives a nonzero `v` lying in `(1 + lambda c_t) R` for every `t` in `T`.
- Lemma B with `G = F`, the element `g`, and `y = b` gives `b v` in `(1 + lambda g) R`.
  `b v ≠ 0` by (D), and `b v` lies in `b R`.

**Item 3.** `alpha u + beta w = alpha (1 + (beta/alpha) w u^-1) u`, and `u` is a unit, so
`(alpha u + beta w) R = (1 + lambda g) R` with `lambda = beta/alpha` and `g = w u^-1 ≠ 1`.
Item 2 applies.

**Equivalence in the definition.** Let `T` be nonempty.
- *(⇒)* Let `Z` separate `T`, and `i < k`. For `t, t'` in `T`,
  `t^-1(I_i) ⊆ (z_(i-1), z_i)` gives `t^-1(q_i) <= z_i`, and
  `t'^-1(I_(i+1)) ⊆ (z_i, z_(i+1))` gives `z_i <= t'^-1(p_(i+1))`. So the maximum is at most
  the minimum. If `q_i = p_(i+1)`, then `t^-1(q_i) = z_i` for any `t` in `T`, so
  `q_i = t(z_i)` is dyadic, because elements of `F` preserve dyadic rationals.
- *(⇐)* Put `z_i = max_(t in T) t^-1(q_i)` for `0 < i < k`. If `q_i < p_(i+1)`, then `q_i`
  is dyadic by (E); otherwise by hypothesis. So `z_i` is dyadic. For `t` in `T` and every
  `i`: `t^-1(q_i) <= z_i` (with `z_k = 1`), and
  `t^-1(p_i) >= min_(t') t'^-1(p_i) >= max_(t') t'^-1(q_(i-1)) = z_(i-1)` (with `z_0 = 0`).
  So `t^-1(I_i) ⊆ (z_(i-1), z_i)`, and `z_(i-1) <= t^-1(p_i) < t^-1(q_i) <= z_i` shows that
  the `z_i` increase strictly.

**Special cases of the target.**
- *Translates.* If `Z` separates `T`, then `s^-1(Z)` separates `T s`, because
  `(t s)^-1(I_i) = s^-1 t^-1(I_i)`. Also `supp(b s) = (supp b) s`.
- *`W_g`.* Elements of `W_g` fix every `p_i` and `q_i`, so `t^-1(I_i) = I_i`. With
  `z_i = q_i` (dyadic by hypothesis), `I_i ⊆ (q_(i-1), q_i)`.
- *`H_i × Z_i`* (all bump endpoints dyadic, `q_0 = 0`, `p_(k+1) = 1`). Let `t = h n` with
  `h` in `H_i` and `n` in `Z_i`.
  - `h` is the identity on `[p_j, q_j]` for `j ≠ i`, and `n` is a product of the `g_j` with
    `j ≠ i`, so `n` maps every `I_j` onto itself and fixes `[q_(i-1), p_(i+1)]`
    pointwise.
  - For `j ≠ i`, `t^-1(I_j) = n^-1 h^-1(I_j) = n^-1(I_j) = I_j`. `h` fixes `q_(i-1)` and
    `p_(i+1)`, so `t^-1(I_i) ⊆ n^-1((q_(i-1), p_(i+1))) = (q_(i-1), p_(i+1))`.
  - With `z_(i-1) = q_(i-1)` (if `i >= 2`), `z_i = p_(i+1)` (if `i <= k - 1`) and
    `z_j = q_j` otherwise, the numbers `z_j` are dyadic and strictly increasing, and
    `t^-1(I_j) ⊆ (z_(j-1), z_j)` for every `j`.
- *`V_Z`.* If `q_i <= z_i <= p_(i+1)` for every `i < k`, elements of `V_Z` map
  `(z_(i-1), z_i)` onto itself, and `I_i` lies in it.

**Remark (where the nesting stops).** One `Z` is fixed throughout. The running multiple
`w_j` lies in `H_j <= V_Z`, so conjugation by its support keeps bump `l` of every member
inside `(z_(l-1), z_l)` and freezes the coordinates not yet released. If two conjugates of
`g` by `supp b` have bump `i` of one ending to the right of the start of bump `i + 1` of the
other, no such `Z` exists, and nothing above applies. This is the non-separated case in the
target's Scope.

**Trust surfaces.**
- Quoted: `thompson-f-binomials-meet-bump-endpoint-stabilizer-ideals` item 1 (the
  requires, itself unreviewed), and left-orderability of `F`.
- Everything else is proved above.
