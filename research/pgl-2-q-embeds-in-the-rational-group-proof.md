---
rg: 2
id: pgl-2-q-embeds-in-the-rational-group-proof
kind: route
title: Reduced integer matrices of fixed determinant are finite, so Moebius maps with rational coefficients have finitely many local actions on the Farey Cantor set
target: pgl-2-q-embeds-in-the-rational-group
requires:
  - pgl-n-q-acts-on-rational-polyhedral-cantor-set
---

Lane gq-deep-free-3, 2026-09-18. Reviewed: gq-referee-a PASS (proof-gap lens, research/artifacts/gq-referee-a-pgl-2-q-embeds-in-the-rational-group.md, 1b7427840), amendments applied; gq-referee-b PASS (citation lens, research/artifacts/gq-referee-b-pgl-2-q-embeds-in-the-rational-group.md, ff17d3b47). Notation as in the target.

**Step 0, the action.** By `pgl-n-q-acts-on-rational-polyhedral-cantor-set`, `PGL_2(Q)` acts
faithfully on `S_2` by homeomorphisms, and `S_2` with the Farey coding is the standard Cantor
set with standard `V`. A cone `C_w` is the doubled arc `S_w([0,∞])`, from `S_w(0)^+` to
`S_w(∞)^-`. The children split this arc at `S_w(1)`: `S_w L` covers `[S_w(0)^+, S_w(1)^-]` and
`S_w R` covers `[S_w(1)^+, S_w(∞)^-]`. Every rational point is interior to only finitely many cones, since Stern–Brocot depth is
finite, and is an endpoint of every deeper cone containing it.

**Step 1, the form of a local action.** Fix `M` with a primitive integral representative of
determinant `D ≠ 0`. `M` preserves `P^1(Q)`, so `M(C_w)` is a doubled arc with endpoints in
`P^1(Q)`. Apart from finitely many `w`, it lies inside one half. There are only two cutting
points, `M^-1(0)` and `M^-1(∞)`, both rational, and each is an endpoint, not an interior
point, of every cone deep enough. For such `w`, let `u` be the longest word with
`M(C_w) ⊆ C_u`. Then `M(S_w(x)) = S_u(N(x))` with `N = S_u^-1 M S_w`, so the local action
`M|_w` is the self-map of the standard coding of `[0,∞]` induced by `N`. It depends only on
`N`. `N` is integral and primitive (multiplying by `SL_2(Z)` preserves the content), with
`det N = D`.

**Step 2, the shape of N.** `N` maps `[0,∞]` homeomorphically into `[0,∞]`. So
`N(x) = (ax+b)/(cx+d)` has no zero or pole in `(0,∞)`. Hence `cx + d` has constant weak sign on
`(0,∞)`, and so does `ax + b`. The two signs agree, because `N(x) >= 0` on `(0,∞)` (N maps into
`[0,∞]`). So after an overall sign change, which leaves `det N` unchanged, `a, b, c, d >= 0`. Maximality of `u` says `N([0,∞])` lies in neither child of the root cone:
it is contained neither in `[0^+, 1^-]` nor in `[1^+, ∞^-]`.

**Step 3, finiteness.**
- If `D > 0`, `N` preserves orientation. The image is `[(b/d)^+, (a/c)^-]`, and the two
  conditions give `a/c > 1` and `b/d < 1`: `a >= c + 1` and `d >= b + 1`. Here `c = 0` counts
  as `a/c = ∞` with `a >= 1`, and `d >= 1`. Then
  `D = ad - bc >= (c+1)(b+1) - bc = b + c + 1`, so `b, c <= D - 1`, and
  `a, d <= ad = D + bc <= D + (D-1)^2`.
- If `D < 0`, `N` reverses orientation. The image is `[(a/c)^+, (b/d)^-]`, and the conditions
  give `c >= a + 1` and `b >= d + 1`. Then `|D| = bc - ad >= (d+1)(a+1) - ad = a + d + 1`, so
  `a, d <= |D| - 1`, and `b, c <= bc = |D| + ad <= |D| + (|D|-1)^2`.

So for all but finitely many `w`, `M|_w` is one of finitely many maps. The remaining `w` add
finitely many more. By the BBMZ criterion `M` is rational, and so is `M^-1 ∈ PGL_2(Q)`. The
map `M ↦ (M on S_2)` is a homomorphism, and it is faithful because the action on the
irrationals is the Möbius action. Standard `V ≤ R`. This proves item 1. Item 2 is item 1
restricted to subgroups, with `BS(1,m) = <x+1, mx>`.

**Item 3.** `M = diag(2^k, 1)` is primitive of determinant `2^k`. By Steps 1–3, all but
finitely many of its local actions are reduced matrices of determinant `2^k`. Distinct `k` give
distinct Möbius maps, hence distinct local actions. So a nucleus containing all but finitely
many local actions of every `diag(2^k,1)` is infinite.

**Item 4.** Elements of `V` are piecewise `S_v S_w^-1 ∈ PSL_2(Z)` on finitely many arcs with
rational endpoints. Such piecewise-`PGL_2(Z[1/P])` homeomorphisms are closed under composition
and inverse, so every element of `<V, PGL_2(Z[1/P])>` is one. A finitely generated subgroup of
`Γ_2` lies in such a group for some finite `P`. A globally Möbius element of it agrees with a
`PGL_2(Z[1/P])` map on an arc. Möbius maps are determined by three points, so the element lies
in `PGL_2(Z[1/P])`.

**Item 5.** `M_2 A M_2^-1 (x) = 2 · (x/2) / ((x/2) + 1) = 2x / (x + 2)`, with matrix
`[[2,0],[1,2]]`. This is primitive of determinant `4`, so it is not in `PGL_2(Z)`. By item 4 of
the required node, an element of `PGL_2(Q)` outside `PGL_2(Z)` agrees with no element of `V`
on any arc. So `M_2 V M_2^-1 ≠ V`.
