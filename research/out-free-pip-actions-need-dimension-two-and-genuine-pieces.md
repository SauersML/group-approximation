---
rg: 2
id: out-free-pip-actions-need-dimension-two-and-genuine-pieces
kind: claim
title: For n at least three, Out(F_n) has no faithful action on the circle by homeomorphisms and no faithful piecewise-integral-projective action on any compact polyhedron of dimension at most one; for n at least four no faithful such action is the projectivization of one linear action, and finite length-function coordinates cannot provide the atlas
requires:
  - piecewise-representative-lifts-are-rigid-under-cheap-moves
distinct_from:
  out-free-sphere-lamination-coordinates-give-a-pip-action: that is the open positive proposal, a piecewise-integral-projective action on measured sphere laminations; this rules out the low-dimensional, linear and length-coordinate versions.
  piecewise-representative-lifts-are-rigid-under-cheap-moves: that compares the band route with the closed-MCG PML route and asks the question; this answers the easy cases of that question.
---

**ESTABLISHED** (lane proof, bh-outfn-2, 2026-09-18). It assembles standard inputs, all
recalled rather than re-read:
- finite subgroups of `Homeo(S^1)` are cyclic or dihedral;
- Thurston: piecewise-`PSL_2(Z)` homeomorphisms with rational breaks are conjugate, by
  Minkowski's `?`, to dyadic piecewise-linear ones;
- Bleak–Salazar-Díaz (Trans. AMS 2013): `Z² ∗ Z` does not embed in Thompson's `V`;
- Koberda (GAFA 2012): high powers of twists generate the right-angled Artin group of their
  disjointness graph;
- Dyer–Formanek–Grossman: `Aut^+(F_2) ≅ B_4/Z(B_4)`;
- Formanek–Procesi (1992): `Aut(F_3)` is not linear;
- Smillie–Vogtmann (1992): no finite set of conjugacy classes has lengths that determine
  points of Outer space, for `n ≥ 3`.

Not reviewed.

**PIP action.** A piecewise-integral-projective (PIP) action on a compact rational
polyhedron `P ⊂ S^{N−1}` (rays of `R^N`) is one where each element is a homeomorphism of `P`
that agrees, on each cell of a finite rational subdivision, with the ray map of a matrix in
`GL_N(Z)`. The closed-MCG host of `board/major-mcg.md` uses `PML ≅ S^{6g−7}` with
train-track charts.

## Statement

Let `n ≥ 3`.
1. **No circle.** `Out(F_n)` has no faithful action on `S^1` by homeomorphisms.
2. **No graphs.** `Out(F_n)` has no faithful PIP action on a compact polyhedron of dimension
   `≤ 1`.
3. **No single linear piece** (`n ≥ 4`). No faithful PIP action of `Out(F_n)` is the ray
   action of one representation `Out(F_n) → GL_N(Z)`. More generally, none factors through a
   finite-dimensional linear representation over any field.
4. **No length atlas.** For no finite set `W` of conjugacy classes is
   `T ↦ [ℓ_T(w)]_{w ∈ W}` injective on `CV_n`. So the tropicalized trace or length
   coordinates, the analogue of the `9g − 9` curve coordinates on PML, cannot serve as a
   finite atlas for `\bar{CV_n}`.
5. **Rank two is the exception, as a calibration.** `Out(F_2) = GL_2(Z)` acts faithfully on
   the circle of rays of `R^2` by one integral projective piece.

So any positive answer lives in dimension `≥ 2`, uses genuinely many pieces, and needs
coordinates other than finitely many translation lengths.

## Proof

1. The sign changes `x_i ↦ x_i^{±1}` give `(Z/2)^n ≤ Aut(F_n)`. No non-identity element is
   inner, since no element of a free group is conjugate to its inverse. So `(Z/2)^n`, with
   `n ≥ 3`, embeds in `Out(F_n)`, and it is neither cyclic nor dihedral.
2. **Such groups sit in `V`.**
   - On a rational edge `[u,v]`, a matrix `A ∈ GL_N(Z)` maps the lattice
     `Z^N ∩ span(u,v)` isomorphically onto `Z^N ∩ span(Au,Av)`. So in lattice bases every
     piece is in `PGL_2(Z)`, with rational breakpoints.
   - Conjugating each edge by `?` makes the action piecewise dyadic-linear on the edges of a
     finite graph. Blowing up dyadic points into left and right copies turns it into a
     faithful action on a Cantor set by finitely many prefix replacements per element.
     Vertices are permuted, and the blow-up is local. So the group embeds in `V`.

   **`Z² ∗ Z` sits in `Out(F_n)`.**
   - `Aut(F_2) ≤ Aut(F_{n−1}) ↪ Out(F_n)` via `φ ↦ [φ ∗ id_{x_n}]`. This is injective: if
     `φ ∗ id = c_u`, then `u` centralizes `x_n` and preserves `F_{n−1}`, so `u = 1`. `Aut^+(F_2) ≅ B_4/Z(B_4)`, which is a
     finite-index subgroup of `Mod(S_{0,5})`.
   - Take disjoint curves `c_1, c_2` and a curve `c_3` meeting both. Koberda's powers
     generate `Z² ∗ Z` inside any finite-index subgroup.
   - `Z² ∗ Z` does not embed in `V` (Bleak–Salazar-Díaz).
3. **One piece means linear.**
   - Suppose each `h_q` is the ray map of one `A_q ∈ GL_N(Z)` on `P`. Let
     `V = span(P)` with lattice `V ∩ Z^N`.
   - `A_{qq'}^{-1}A_qA_{q'}` fixes every ray of `P`. It preserves `V` and its lattice. Every
     rational point of `P` is an eigenvector with a positive rational eigenvalue, which is an
     algebraic integer and hence a positive integer. These eigenvectors span `V`, so the
     element is diagonalizable on `V` with positive integer eigenvalues of product `±1`.
     So it is the identity on `V`.
   - So `q ↦ A_q|_V` is a homomorphism. It is injective because the action is faithful.
     So `Out(F_n)` would be linear.
   - But `Aut(F_3) ≤ Aut(F_{n−1}) ↪ Out(F_n)` for `n ≥ 4` (as in item 2), and `Aut(F_3)` is not
     linear. Linearity passes to subgroups.
4. This is Smillie–Vogtmann. The trace or length coordinates of any point of
   `\bar{CV_n}` restricted to `CV_n` are exactly the lengths `ℓ_T(w)`.
5. Clear: `−I` acts as the antipodal map. `∎`

## Lesson for general BH

A host borrowed from another group must match that group's **honest coordinates**.
`Mod(S_g)` imports PML: dimension `6g−7`, finitely many integral train-track charts. For
`Out(F_n)` every cheap substitute fails:
- circles and graphs fail (a Thompson-group obstruction, `Z² ∗ Z ⊄ V`);
- single linear pieces fail (non-linearity);
- finite length coordinates fail (Smillie–Vogtmann).

What is left is a genuinely piecewise action in dimension `≥ 2` on coordinates of a
different kind: splittings rather than conjugacy classes. That is the proposal
`out-free-sphere-lamination-coordinates-give-a-pip-action`.
