---
rg: 2
id: zn-rips-top-shell-formula-link-collapse
kind: claim
title: The formula link collapse K u | e_j + e_k needs a within-link order, but order-free certificates with other witnesses delete every top shell for r ≤ 6
distinct_from:
  zn-rips-contractible-at-every-scale-r-ge-n: that is the uniform statement for every r ≥ n; this proves an obstruction to one route to it and checks a replacement at the scales r ≤ 7
  z8-rips-scale-11-reduces-to-top-shell-link-collapses: that node reduces (8, 11) to (K) moves on its set T and checks samples of the formula lines against one fixed state; this shows that no proof of those lines can treat the bad points one at a time, and checks order-free certificates for T by other witnesses on a sample
  zn-rips-top-shell-sign-hull-certificates: that node proves the certificate scheme (a scale-free sufficient condition); this is the record of which witnesses satisfy it at which scales, and of where the formula witness fails
---

Notation is that of `zn-rips-top-shell-sign-hull-certificates`: level `k`, radius `r`, `E = e_k`, `Lmax = Lmax_k`,
`Top`, `Z_0`, the bad set `Bad(u,w)`, and `F`-certificates. For `u ∈ Z_0` let `j(u)` be its last nonzero index, and
call `w_f(u) = e_{j(u)} + e_k` the **formula witness**. Its bad set is described by Claim 4 of that node (with
`i = j(u)` and `s = +1`, since `u ≻ 0`).

**Claim.**
1. *(The formula lines hold in order.)* For `(k, r) ∈ {(4,4), (4,5), (4,6), (5,5), (5,6), (5,7), (6,6), (6,7)}`, the
   sequence of moves `K u | w_f(u)`, one for each `u ∈ Z_0`, is valid from `C = Lmax_k`, both in the order of
   decreasing `j(u)` and in the order of increasing `j(u)`. (33 to 1765 lines per case.)
2. *(No order-free proof of the formula lemma.)* At `(k, r) = (6, 6)` take `u = (2,1,1,1,1,0)`, `w = w_f(u) = e_5 + e_6`
   and `b = (2,1,1,1,0,0)`. Then `b ∈ Bad(u,w)` and `|b| = 5`, so `b` lies in every state `C ⊇ Lmax ∖ Z_0`. In
   every such state that contains `u`, no point `v ≠ b` of `S = N(u) ∩ C` with `v ∈ hull(0,u,b,E)` has
   `N[b] ∩ S ⊆ N[v]`. So `b` is never the first point that `K u | w` removes from `N(u) ∩ C`. The same holds for 32
   pairs `(u, b)` at `(6, 6)`, one per `u`. It also holds for at least 370 of the 5,418 points `u ∈ Z_0` at `(7, 7)`
   and for at least 210 of a 480-point sample at `(7, 8)`. At `(8, 11)` it holds for the point
   `u = (-2,2,2,-1,2,1,1,0)` of `T`, with 12 such bad points `b`.
3. *(Order-free certificates exist at small scales.)* For every `2 ≤ k ≤ r ≤ 6`, and for `k ≤ 6`, `r = 7`:
   - every `u ∈ Z_0` has a `Z_0`-certificate;
   - every unbalanced `u ∈ Top ∖ Z_0` has a `Top`-certificate.

   At `(7, 7)` every `u ∈ Z_0` has a `Z_0`-certificate. The witnesses have norm at most 3, except for 88 points
   `u ∈ Z_0` at `(7,7)` that need norm 7 and 12 points of `Top ∖ Z_0` at `(6,6)` that need norm 5.
3′. *(The scheme stops at `(7, 7)`.)* At `(k, r) = (7, 7)`, exactly 824 of the 4,816 unbalanced points of `Top ∖ Z_0`
   have no `Top`-certificate. All 824 have `x_7 = 1`. They still have none for the larger class
   `F = { x ∈ Top : x_7 ≤ 1 }`, which would delete the shell `x_7 = 1` before the shells `x_7 ≥ 2`. So condition (b)
   of Claim 6 of the sign-hull node fails at level 7 for `r = 7`, and that claim gives nothing for `n ≥ 7`, `r = 7`.
4. *(The argmax witness.)* Let `w_a(u) = s e_i + e_k`, with `i` the first index of maximal `|u_i|` and `s = sgn u_i`.
   It is a `Z_0`-certificate witness for every `u ∈ Z_0` at `(3,3)`–`(3,5)`, `(4,4)`–`(4,7)`, `(5,5)`–`(5,8)`,
   `(6,6)`–`(6,8)` and `(7,8)`, with steps `v_b ∈ b + {|δ| ≤ 2}` or found by a box search. At `(7, 7)` it fails
   for 1,584 of the 5,418 points.
5. *(The case `(8, 11)`.)* Every point of the set `T` of `z8-rips-scale-11-reduces-to-top-shell-link-collapses`
   lies in `Z_0`. No line of that node's (D) prefix or tail has its deleted point or its witness in `T`. So by
   Claim 2 and §7 of `zn-rips-top-shell-sign-hull-certificates-proof`, a `Z_0`-certificate for each of its
   53,312 points finishes `(8, 11)`. On a 59-point sample of `T`, every point has one, with a witness of norm
   at most 4. The formula witness gives none for `u = (-2,2,2,-1,2,1,1,0)`, and the argmax witness fails for 6 of
   that point's bad points.

**Consequences.**
- By 3 and Claim 6 of `zn-rips-top-shell-sign-hull-certificates`, `VR(Z^n, d_1; r)` is contractible for
  `2 ≤ n ≤ r ≤ 6` and for `n ≤ 6`, `r = 7`, by one order-free local scheme.
- The Formula Link-Collapse Lemma (each `u ∈ T` is deleted by `K u | w_f(u)` in a fixed class order) is true
  wherever it was tested (1). By 2, however, no argument that handles the bad points of a link one at a time can
  prove it, and neither can any choice of order on `T`, since the obstruction holds in every state
  `C ⊇ Lmax ∖ Z_0`. A proof would have to control the order of removals inside each link.
- The `Z_0` half of the scheme ((a) of Claim 6) holds at every scale tested, including `(7, 7)` and the sample at
  `(8, 11)`, with non-formula witnesses. The `Top ∖ Z_0` half ((b)) fails at `(7, 7)` by 3′. So a uniform proof
  can use certificates for `Z_0`, but it needs another deletion (an order inside the shell `x_k = 1`, or witnesses
  outside `hull(0,u,E)`) for the unbalanced points with `x_k = 1`.
- At `(8, 11)` only `T ⊆ Z_0` is left, so (b) is not needed there (Claim 5).

**Still only computational.**
- Levels `k ≤ 4` at `r = 8`, and (b) at `r = 8`.
- The `Z_0`-certificates for all of `T` at `(8, 11)`. Only 59 of its 53,312 points are checked.

## Attempts
- 2026-09-19 (w11-103): tried to prove the Formula Link-Collapse Lemma point by point, by giving each bad point
  of `K u | e_j + e_k` a dominator that is present whatever was deleted before `u`. This is impossible (Claim 2),
  at `(6, 6)` and at a point of `T` at `(8, 11)`. The class order on `T` cannot help, since the obstruction holds
  in every state. The replacement is order-free sign-hull certificates with other witnesses (Claims 3–5). They
  cover `Z_0` everywhere tested, but they do not cover the top-shell points with `x_k = 1` at `(7, 7)` (3′).

Proof: route `zn-rips-top-shell-formula-link-collapse-proof`.
