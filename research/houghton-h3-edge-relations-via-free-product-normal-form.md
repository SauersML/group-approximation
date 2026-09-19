---
rg: 2
id: houghton-h3-edge-relations-via-free-product-normal-form
kind: route
title: Reduce each three-ray edge relation to its free-product normal form, then close with one literal family relator
target: houghton-h3-edge-relations-reduce-to-five-families
requires: []
artifacts:
  - experiments/houghton-h3-theorem-a-2026-09-17/verify_theorem_a.py
  - experiments/houghton-h3-theorem-a-2026-09-17/verify_theorem_a.out
---

Complete proof, for all `R`. The machine check (`verify_theorem_a.py`, output in
`.out`) replays every derivation below for all 8 route functions at depth `<= 20`.

**Lemma N (normal form).** Let `G*` be the free product of three infinite cyclic
groups `⟨λ_xy⟩`, one for each unordered pair of rays, with `λ_yx` read as
`λ_xy^(-1)`, and three groups `⟨τ_x⟩` of order 2. The words

- `λ_xy λ_yx`,
- `τ_x τ_x`,
- `λ_xy^(-1) · λ_yx^(-1)`, and `τ_x^(-1) τ_x^(-1)`, which are the conversions of formal
  inverses

have length 2 and are trivial in `H_3`, so they lie in `Q`. Hence every word `w` reaches
its cyclically reduced normal form `ν(w)` in `G*` with `<= 3|w|/2` relator applications:
at most one conversion per letter and at most `|w|/2` cancellations. If `ν(w)` is a cyclic
rotation of `ν(W)^(±1)`, then `Area(w) <= Area(W) + 3(|w| + |W|)/2`.

**Notation.** In `G*`, with `a = λ_(x c(x))`:

- `Ed(t_x(j)) = a^(j-1) τ_x a^(-(j-1))`;
- `Ed(σ_{x,y}) = λ_yx τ_x λ_yx^(-1)`;
- `D^u_x(k) = λ_xu^k τ_x λ_xu^(-k)`.

A ray edge `t_x(j)` has depth `j + 1`, so `j <= R - 1`.

**Part 1: edge relations.**

- (E1). `ν(Ed(e)^2) = g τ^2 g^(-1) = 1`, so the cost is `<= 3(2R-1)`.
- (E3). The pairs sharing exactly one vertex are `(t_x(j), t_x(j+1))`,
  `(t_x(1), σ_{x,y})` and `(σ_{x,y}, σ_{x,z})`, in either order.
  - The last two have length `<= 18`. After conversions they are relators of `Q`.
  - For the first, `ν` is the `a^(j-1)`-conjugate of the `j = 1` relation, whose normal
    form has length `<= 18`. It is trivial, hence one relator of `Q`.
  - The cost is `<= 9(2R-1) + 1`.
- (E2)(i), `e = t_x(i)`, `f = t_x(j)` with `|j - i| = m >= 2`. Conjugating by
  `a^(i-1)` in `G*` gives `[τ_x, a^m τ_x a^(-m)] = ν(F_3(m))`, or its inverse if
  `i > j`. The cost is `<= F_3(m) + 3(8R + 4R + 4)/2 <= Φ(R) + 30R`.
- (E2)(ii)–(iv). These are literally `B_3(i,j)` and `C_3(j)`.
- (E2)(v). With three top vertices, two top edges always meet, so there is no instance.

**Part 2: Lemma 4.2.** Let `s = λ_zw`, and let `x` be the third ray. The letter `s` moves
only rays `z` and `w`, and every edge falls into one of the following cases.

- `t_x(j)`. Here `e' = e`, and `ν(s^(-1) Ed(e) s Ed(e)^(-1)) = ν(D_3(j))`, since
  `s^(-1) = λ_wz` in `G*`. The cost is `<= Φ(R) + 12R`.
- `t_y(j)` with `y ∈ {z,w}` (`j >= 2` if `y = z`). Let `o` be the other ray of `{z,w}`.
  Then `e' = t_z(j-1)` if `y = z`, and `e' = t_w(j+1)` if `y = w`.
  - If `c(y) = o`, then in `G*`

    ```text
    λ_wz · λ_zo^(j-1) τ_z λ_zo^(-(j-1)) · λ_zw = λ_zw^(j-2) τ_z λ_zw^(-(j-2))   (y = z),
    λ_wz · λ_wz^(j-1) τ_w λ_wz^(-(j-1)) · λ_zw = λ_wz^j τ_w λ_wz^(-j)             (y = w).
    ```

    So `ν = 1`, and the cost is `<= 3(4R+4)/2`.
  - If `c(y) = x`, first replace `Ed(e) = D^x_y(k_1)` by `D^o_y(k_1)`. Then replace
    `Ed(e')^(-1) = D^x_y(k_2)^(-1)` by `D^o_y(k_2)^(-1)`. Each replacement is literally a
    member of `R_3`, with `k_1, k_2 <= R - 1`. After them `ν = 1`, as in the previous
    case. The cost is `<= 2Φ(R) + 6R + 6`.
- `t_z(1)`, where `e' = σ_{z,w}`.
- `σ_{z,w}`, where `e' = t_w(1)`.
- `σ_{z,x}`, where `e' = σ_{w,x}`.
- `σ_{w,x}`, where `e^s = ((w,2),(x,1))` is not an edge. This is the second alternative,
  and the word used is `Ed(t_w(1)) Ed(σ_{w,x}) Ed(t_w(1))`.

In the last four cases the relation has length `<= 2 + 3 + 9 = 14 <= 40`. It is one
relator of `Q` plus at most 14 conversions.

The case list is exhaustive. The relation words have length `<= 6(2R-1)`, and each uses
at most two family relators, each of index `<= R`. This proves both parts of the claim.
∎

**Machine check.** The verifier has four kinds of step:

- free reduction and rotation;
- `Q`-steps, checked by evaluating both sides on all points of depth `<= max length + 3`,
  with `|u| + |v| <= 40` enforced;
- `CANON`, the count of Lemma N;
- `M`-steps, accepted only when `ν(v u^(-1))` is a rotation of `ν(W)^(±1)`, where the
  literal family word `W` is built from the table.

It rejects four planted invalid steps. It derives 31680 relations and measures
`<= 8R + 2` `Q`-steps per relation.
