---
rg: 2
id: circle-groups-with-divisible-free-germs-omit-gl-n-q
kind: claim
title: Germ-local form - if every point-germ group of a circle or interval group has no divisible subgroup, divisible abelian subgroups have N = C, so GL_n(Q), Aff(Q), U_3(Q) do not embed, even with breakpoints accumulating at singular points
distinct_from:
  pp-circle-divisible-subgroups-act-freely: that assumes every element is Lambda-piecewise with finitely many breakpoints for a divisible-free Lambda; this assumes only that the point-germ groups are divisible-free, so elements may have infinitely many breakpoints accumulating at points with divisible-free germ groups (finite germ extensions of those hosts). The argument is the same.
  pp-circle-and-lift-hosts-miss-gl-n-q: that also covers the lifts to R through the translation number (T-bar) and the [A,A] criterion, which this does not; this adds germ extensions of the circle hosts and index-2 overgroups with orientation-reversing elements.
  germ-extensions-omit-standard-gl-n-q: that excludes only the standard (analytic) copy of GL_n(Q) in piecewise-projective and piecewise-affine groups, and leaves nonstandard copies open; this excludes every copy, standard or not, from circle and interval hosts.
  lifts-add-no-unipotent-divisibility: that excludes central and covering lifts of Q-free groups, such as T-bar; this excludes circle groups with divisible-free germs, whether or not they contain (Q,+).
  piecewise-analytic-circle-square-conjugate-has-parabolic-ends: that describes the fixed points of an element conjugate to its square in PA(S^1); this uses rotation numbers and germ groups to exclude divisible subgroups normalized non-centrally.
  higman-group-embeds-in-no-piecewise-analytic-circle-group: that excludes Higman's group from PA(S^1) by the same kind of one-dimensional argument; this excludes GL_n(Q), Aff(Q) and U_3(Q) under a germ hypothesis.
  fg-piecewise-linear-hosts-omit-natural-gl-n-q: that is the derivative argument against natural affine gluings; this is dynamical and covers abstract embeddings.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this rules out the one-dimensional hosts (circle, interval, line with divisible-free germs at infinity) for every n >= 2.
---

**ESTABLISHED** through `circle-groups-with-divisible-free-germs-omit-gl-n-q-proof`. Elementary; not
independently reviewed; no priority is claimed for the rotation-number and germ arguments themselves.

**Relation to `pp-circle-divisible-subgroups-act-freely`.** That claim (lane gq-pp-psl2q) proves the same
conclusions for groups whose elements are piecewise, with finitely many breakpoints, in a group without
divisible abelian subgroups, and `pp-circle-and-lift-hosts-miss-gl-n-q` extends them to lifts to `R`. This
claim is the germ-local form of the argument. Its hypothesis (DF) concerns only the germ groups of point
stabilizers. So it also covers groups whose elements have infinitely many breakpoints accumulating at finitely
many singular points, provided the germ groups at those points are divisible-free. This is the case "infinitely
many breakpoints" that attempt 10 of the root lists as not covered, in the form that arises for finite germ
extensions. It also allows orientation-reversing elements (Item 3). It does not cover `T-bar`, which fails (DF)
at `±∞`; that case is `pp-circle-and-lift-hosts-miss-gl-n-q` (a), or `lifts-add-no-unipotent-divisibility`.

## Statement

Let `Γ <= Homeo_+(S^1)`. For `y in S^1` let `G^+_y(Γ)` and `G^-_y(Γ)` be the groups of right and left germs at
`y` of the stabilizer `Stab_Γ(y)`. Assume

> **(DF)** for every `y in S^1`, neither `G^+_y(Γ)` nor `G^-_y(Γ)` contains a nontrivial divisible subgroup
> (for example, each is residually finite).

Then:

1. **(Rotation-null divisible subgroups are trivial.)** If `D <= Γ` is divisible and the rotation number
   vanishes on `D`, then `D = 1`.
2. **(Normalizers of divisible abelian subgroups.)** If `A <= Γ` is abelian and divisible, then
   `N_Γ(A) = C_Γ(A)`.
3. **(Excluded subgroups.)** Let `Γ' <= Homeo(S^1)` contain `Γ` as a subgroup of index at most 2, with
   `Γ = Γ' ∩ Homeo_+(S^1)`. Then `Γ'` contains no subgroup isomorphic to any of
   `GL_n(Q)`, `SL_n(Q)`, `PGL_n(Q)`, `PSL_n(Q)` for `n >= 2`, `Aff(Q) = Q x| Q^x`, the Borel group `B_2(Q)`, the
   Heisenberg group `U_3(Q)`, or any `Q x|_a Z` with `a in Q^x \ {1, -1}` (and `Γ` itself contains no
   `Q x|_(-1) Z` either).
4. **(Interval and line.)** The same conclusions hold for `Γ <= Homeo_+([0,1])` satisfying (DF) at every point
   of `[0,1]` (one-sided germs at the endpoints), and for `Γ <= Homeo_+(R)` satisfying (DF) at every point and
   for the germs at `+∞` and `-∞`.

## When (DF) holds

- **Finitely piecewise groups with a divisible-free piece group.** Suppose there are a group `L <= Homeo(S^1)`
  with the identity principle (an element that is the identity on a nonempty open set is trivial) and a
  subgroup `Δ <= L` with no nontrivial divisible subgroup, such that every `γ in Γ` agrees, on each component
  arc of `S^1 \ B_γ` for some finite `B_γ`, with an element of `Δ`. Then the right germ at `y` of
  `γ in Stab_Γ(y)` is the germ of the unique piece `δ in Δ` of `γ` on `[y, y+ε)`, and `γ ↦ δ` embeds
  `G^+_y(Γ)` in `Δ`; likewise on the left. So (DF) holds.
  - **Piecewise projective.** `L = PSL_2(R)` on `RP^1`. If `Γ` is finitely generated, the pieces of all its
    elements lie in the subgroup generated by the finitely many pieces of the generators
    (`germ-extensions-omit-standard-gl-n-q`, Item 3), a finitely generated linear group, residually finite by
    Mal'cev. If the pieces lie in `PSL_2(A)` for a finitely generated subring `A <= R`, then `Δ` is
    residually finite even when `Γ` is not finitely generated: the adjoint representation embeds `PSL_2(A)`
    in `GL_4(A)`, which is residually finite by Mal'cev.
  - This covers Thompson's `T` in its piecewise-`PSL_2(Z)` model, Lodha's finitely presented infinite simple
    group `S` (arXiv:1710.06220v2, Theorem 1.1; generated by `T` and one piecewise projective homeomorphism),
    the Lodha--Moore group (arXiv:1308.4250: "a finitely presented subgroup of Monod's group of piecewise
    projective homeomorphisms of R"), and Monod's groups `H(A)` for finitely generated subrings `A <= R`
    (Monod, arXiv:1209.5229: homeomorphisms of `RP^1` fixing `∞`, piecewise in `PSL_2(A)` with finitely many
    pieces and breakpoints in `P_A`).
- **PL circle groups.** A right germ at a fixed point of a PL homeomorphism is determined by its right slope,
  so `G^±_y(Γ)` embeds in the slope group `Λ <= R_{>0}`. (DF) holds whenever `Λ` has no nontrivial divisible
  subgroup: for example `Λ` finitely generated (Thompson's `T`, the Stein--Thompson groups `T_{n_1,...,n_k}`)
  or `Λ <= Q_{>0}` (a free abelian group).
- **Finite germ extensions.** A group that is locally in one of the groups above except at finitely many
  singular points per element satisfies (DF) as soon as its germ groups at the singular points have no
  nontrivial divisible subgroup.

## Relation to the other obstructions

- **Distortion (root O4) does not reach these hosts.** They have distorted cyclic subgroups: Lodha's `S`
  contains `BS(1,2)` (`piecewise-analytic-circle-square-conjugate-has-parabolic-ends`, Sharpness), and Monod's
  `H(Z[1/2])` contains `x -> x+1` and `x -> 4x`, hence `BS(1,4)`. So the distortion obstruction, which kills
  `VA`, says nothing about them. For the finitely-breakpoint hosts, `pp-circle-and-lift-hosts-miss-gl-n-q`
  already excludes `GL_n(Q)` for every `n >= 2` and every embedding. This claim extends that to their finite
  germ extensions with divisible-free singular germ groups. It does not touch the Cantor-set germ extensions
  for which attempt 6 of the root leaves `n = 2` open outside `VA`.
- **Standard copies.** `germ-extensions-omit-standard-gl-n-q` excludes the analytic copy. This claim excludes
  nonstandard copies too, as in Belk--Hyde--Matucci's `Q <= T-bar`, where the element for `1/k` is a lift of
  torsion, not a translation.
- **Sharpness.**
  - (DF) cannot be dropped on the line: `Aff^+(Q) = Q x| Q_{>0}` acts naturally on `R` with germ groups at
    finite points isomorphic to `Q_{>0}` (free abelian). It fails (DF) only at `±∞`, where the translation
    germs form a copy of `(Q,+)`; so Item 4 needs the hypothesis at infinity.
  - `T-bar` contains `(Q,+)` and fails (DF) at `±∞`, where its germs are faithful.
  - Divisible subgroups themselves are not excluded: the rational rotations form a copy of `Q/Z` with
    trivial point stabilizers, so they satisfy (DF), with nonzero rotation numbers. Item 1 excludes only
    rotation-null divisible subgroups, and Item 2 only non-central normalizers.

## What this leaves open

The argument is one-dimensional: rotation numbers supply the fixed points, and connectedness spreads the
trivial germs. On totally disconnected spaces the second step fails, and indeed `(Q,+) <= 2V` (Kojima--Sheng,
arXiv:2603.18410v3). In dimension at least 2 the first step fails. The surviving host
shapes for `GL_2(Q)` are therefore zero-dimensional (Cantor) or higher-dimensional.
