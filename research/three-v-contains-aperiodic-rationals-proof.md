---
rg: 2
id: three-v-contains-aperiodic-rationals-proof
kind: route
title: Encode the minimal SMART moving-tape map as an element of 2V and run the mixed-radix root tower over it in 3V
target: three-v-contains-aperiodic-rationals
requires:
  - rationals-embed-in-brin-thompson-group-2v
---

**Model of a machine.** A reversible Turing machine in the moving-tape model is a
homeomorphism `F` of `X = Σ^Z × Q`, with finite `Σ` and `Q`, and an `r >= 0` such
that the following holds. For each local pattern `w = (q, c_{-r} … c_r)`, the
cylinder `Z_w` is sent by `F` as follows: the window is rewritten to a word
`c'_{-r} … c'_r` and the state to `q'`, both determined by `w`; cells outside
`[-r, r]` are unchanged; and the configuration is shifted by some `d ∈ [-r, r]`,
also determined by `w`. So `F(c)_i = c'_{i+d}`, where `c'` agrees with `c` off
`[-r, r]`. This is the model of Barbieri–Kari–Salo as described in arXiv:2303.17270
(abstract: machines "can only modify the tape at a bounded distance around the head,
change the state and move the head in a bounded way"). For SMART, `F` is minimal by
the source quoted in the claim.

**Item 1: the conjugacy.**
- Fix complete prefix codes `κ: Σ -> {0, 10, 11}` (for `|Σ| = 3`) and
  `β: Q -> {00, 01, 10, 11}` (for `|Q| = 4`).
- Define `φ: X -> C × C` by `φ(c) = (L, R)`, with
  `L = κ(c_{-1}) κ(c_{-2}) κ(c_{-3}) ⋯` and `R = β(q) κ(c_0) κ(c_1) ⋯`.
- Complete prefix codes parse every infinite word uniquely, so `φ` is a
  homeomorphism.
- Put `T = φ F φ^-1`. For a pattern `w`,
  `φ(Z_w) = C(u_L) × C(u_R)`, with `u_L = κ(c_{-1}) ⋯ κ(c_{-r})` and
  `u_R = β(q) κ(c_0) ⋯ κ(c_r)`. These bricks partition `C × C`.
- On `φ(Z_w)` we have `T(u_L x, u_R y) = (v_L x, v_R y)`, with
  `v_R = β(q') κ(c'_d) ⋯ κ(c'_r)` and `v_L = κ(c'_{d-1}) ⋯ κ(c'_{-r})`. The word
  `v_L` is empty if `d = -r`.
  - *Check.* The new right half is `c'_d, c'_{d+1}, …`. Its entries beyond `r` are the
    old `c_{r+1}, …`, encoded by `y`. The new left half is `c'_{d-1}, …, c'_{-r}`,
    followed by the old `c_{-r-1}, …`, encoded by `x`.
- So `T` is a prefix replacement on every brick of a finite brick partition. `F` is a
  bijection, so the image bricks `C(v_L) × C(v_R)` are pairwise disjoint and cover
  `C × C`, which means they form a partition too.
- By Brin's definition, as recalled in `rationals-embed-in-brin-thompson-group-2v-proof`,
  `T ∈ 2V`.
- `T` is conjugate to the minimal homeomorphism `F` of the infinite space `X`.
  - A periodic orbit would be a finite, closed, invariant, proper subset, so `T` has
    no periodic point.
  - If `T^N = id` for some `N >= 1`, every point would be periodic. So `T` has infinite
    order.

**Item 2: the tower.**
- *(O1′).* Let cones `Y_j` partition `C`, let cones `Y'_j` partition `C`, let their
  prefixes be `y_j` and `y'_j`, and let `g_j ∈ 2V`. Then
  `(x, y_j w) ↦ (g_j(x), y'_j w)`, with `x ∈ C^2`, lies in `3V`: refine each box
  `C^2 × C(y_j)` by the domain bricks of `g_j`. This is (O1) of the landed proof, with
  `2V` and `3V` in place of `V` and `2V`.
- Define `s_0 = T × id`. For `n >= 1` define `s_n` by the landed formula, with `t`
  replaced by `T`:
  - `s_n(x, y) = (T^q(x), c_{2,d'_1} ⋯ c_{n+1,d'_n} w)`;
  - `q ∈ {0, 1}` and `d'` come from `N_n(y) + 1 = q (n+1)! + N'`.
  By (O1′), `s_n ∈ 3V`.
- The landed verification of `s_n^{n+1} = s_{n-1}` uses only the digit arithmetic in
  the counter coordinate, and the fact that the base map is applied once on each
  overflow. It holds verbatim. The same goes for the injectivity of
  `⟨s_n⟩ -> (1/(n+1)!) Z`, which needs only that `T` has infinite order. So
  `Q_T = ∪_n ⟨s_n⟩ ≅ Q`, and `s_n^{(n+1)!} = s_0`.
- *No periodic points.* Let `h ∈ Q_T \ {1}`. Then `h = s_n^j` with `j ≠ 0`, for some
  `n`, and `h^{(n+1)!} = s_0^j`.
  - If `h^p z = z` for some `p >= 1` and `z = (x, y)`, then
    `s_0^{jp} z = h^{p (n+1)!} z = z`.
  - That is, `T^{jp} x = x` with `jp ≠ 0`. So `x` is a periodic point of `T`, which
    contradicts item 1. ∎

**Item 3** is immediate. Exponent-flatness and the conditions in items 1–3 of
`bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets` quantify over periodic
points, and there are none. The periodic set is empty, which is open, and the
aperiodic core is `C^3`.
