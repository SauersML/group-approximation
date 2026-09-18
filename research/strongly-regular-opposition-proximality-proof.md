---
rg: 2
id: strongly-regular-opposition-proximality-proof
kind: route
title: Proof that chambers at infinity of a locally finite Euclidean building carry an open dense opposition relation on which strongly regular elements contract uniformly
target: strongly-regular-building-elements-are-opposition-proximal
requires:
  - opposition-ping-pong-criterion-gives-mixed-identity-freeness
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

Lane proof (bh-testcases, 2026-09-18). It is elementary modulo the standard facts
(I1)–(I7) below, which were not re-read at source. No priority is claimed.

## Setting and imported facts

- `X` is a locally finite thick Euclidean building with its complete apartment system,
  `Z = Ch(∂X)`, and `O` is the opposition relation on `Z`.
- For a point `y` and `c ∈ Z`, `Q(y, c)` is the sector based at `y` pointing to `c`. Its
  **germ** at a special vertex `y` is a chamber of the spherical building `Lk(y)`.
- In an apartment `A` with Weyl cones `C_c` (`c ∈ Ch(∂A)`),
  `Q(y, c) = y + C_c`.

The imported facts:

- **(I1) Opposite germs.** If `y` is special and the germs of `Q(y, c)` and `Q(y, d)` are
  opposite in `Lk(y)`, then `Q(y, c) ∪ Q(y, d)` lies in an apartment. In particular `c`
  and `d` are opposite.
- **(I2) Common subsector.** Two apartments containing `c ∈ Z` in their boundaries share
  a sector `Q(y, c)` with `y` special.
- **(I3) Cone topology.** For a special vertex `y`, the sets
  `U_y(d_0, R) = {d : Q(y,d) ∩ B(y,R) = Q(y,d_0) ∩ B(y,R)}`, for `R > 0`, form a
  neighbourhood basis at `d_0`, and the topology doesn't depend on `y`. `Z` is compact
  Hausdorff. For small `R`, `U_y(d_0, R)` is the set of `d` with the same germ at `y`.
- **(I4) Apartments.**
  - Apartments are convex and isometrically embedded.
  - The intersection of two apartments is combinatorially convex, an intersection of
    roots. So it contains the Weyl-convex hull `(o + C) ∩ (y − C)` of any two of its points
    `o, y`, where `C` is the Weyl cone containing `y − o`.
  - Two apartments are related by an isometry that fixes their intersection pointwise.
  - Any two chambers of `Z` lie in a common apartment's boundary.
  - Opposite chambers of `Z` lie in exactly one apartment.
- **(I5)** In a thick spherical building, any two chambers have a common opposite
  chamber.
- **(I6)** At a special vertex `y`, every chamber of `Lk(y)` is the germ of some sector
  `Q(y, c)`.
- **(I7) Strongly regular elements.** A strongly regular hyperbolic `a` has a unique
  translation apartment `A`. On `A` it acts as translation by a vector `τ` in the
  interior of `C_(c_+)`, it fixes `c_±`, and `C_(c_-) = −C_(c_+)`. Type-preserving `a` maps
  special vertices to special vertices.

## Part (a)

- **`O` is open.** Let `(c, d) ∈ O`, let `A` be the apartment containing both, and let
  `y ∈ A` be special. In `A` the sectors `y + C_c` and `y + C_d = y − C_c` have opposite
  germs. By (I3), `U_y(c, ε) × U_y(d, ε)` is a neighbourhood of `(c, d)` consisting of pairs
  with the same germs at `y`. By (I1) it lies in `O`.
- **`O(c)` is dense.** Let `V = U_o(d_0, R)` be a basic open set, with `o` special.
  - Choose an apartment `A_0` containing `Q(o, d_0)`, and a special vertex `y` in it with `y − o`
    in the interior of `C_(d_0)` and `|y − o|` so large that
    `(o + C_(d_0)) ∩ B(o, R) ⊆ y − C_(d_0)`.
  - Let `γ` be the germ of `Q(y, c)` and `η` the chamber of `Lk(y)` containing the direction
    of `o − y`. By (I5) and (I6) pick `d` with germ `δ` at `y` opposite both `γ` and `η`.
  - Then `d` is opposite `c`, by (I1).
  - **`d` lies in `V`.** Let `e` be the chamber of `∂A_0` with germ `η` at `y`. Then
    `o ∈ Q(y, e)`. By (I1) some apartment `A_1` contains `Q(y, e) ∪ Q(y, d)`. In `A_1`, `d` is
    opposite `e`, so `y − o ∈ int C_d`. So both truncated sectors `Q(o, d) ∩ B(o, R)` and
    `Q(o, d_0) ∩ B(o, R)` lie in the Weyl-convex hull of `o` and `y`.
    - That hull lies in `A_0 ∩ A_1` (I4), and the isometry `A_1 → A_0` fixes it pointwise.
    - Inside the hull both truncated sectors are the same set `(o + C) ∩ B(o, R)`.
    - So `d ∈ V`.
- Compactness and the Hausdorff property are (I3). Each `O(c)` is open and dense in the
  infinite space `Z`, so it has at least two points, which is (PR1).

## Part (b)

Fix a special vertex `v ∈ A`. Let `ρ > 0` be the distance from `τ` to the boundary of the
cone `C_(c_+)`.

- **Witness radius.** For `d ∈ O(c_-)`, let `R(d)` be the infimum of `|v − y|` over special
  `y ∈ A` for which some apartment `A_d ∋ c_-, d` contains `Q(y, c_-) = y + C_(c_-)`. It is
  finite by (I2).
- **`R` is locally bounded.**
  - Take `d`, a witness `y` with `|v − y| ≤ R(d) + 1`, and `A_d`.
  - In `A_d`, `d` is opposite `c_-`, so the germs at `y` of `Q(y, d)` and `Q(y, c_-)` are
    opposite.
  - Let `d'` share the germ of `d` at `y`; this is an open set by (I3).
  - By (I1), an apartment `A'` contains `Q(y, d') ∪ Q(y, c_-)`. It contains `c_-` and `d'`,
    and `Q(y, c_-) ⊆ A`. So `R(d') ≤ R(d) + 1`.

  Hence `R_K = sup_K R < ∞` on every compact `K ⊆ O(c_-)`.
- **Uniform contraction (PR2).** Let `U ∋ c_+` be open. By (I3) choose `R'` with
  `U_v(c_+, R') ⊆ U`, and choose `n_0` with `n_0 ρ ≥ R_K + 1 + R'`. Let `n ≥ n_0` and
  `d ∈ K`, with witness `y` and apartment `A_d` as above.
  - **The shared region.** `a^n A_d` contains `c_-`, `a^n d` and
    `a^n(y + C_(c_-)) = y + nτ + C_(c_-)`. The latter lies in `A`. Since
    `B(0, nρ) ⊆ nτ + C_(c_-)`, it contains `B_A(v, R')` and `v + C_(c_-)`.
  - **The isometry.** Let `φ : a^n A_d → A` be the isometry fixing `A ∩ a^n A_d` (I4). It fixes
    `B_A(v, R')` pointwise, so the `R'`-balls around `v` in the two apartments coincide.
  - **The sectors.** In `a^n A_d`, `a^n d` is opposite `c_-`. So `Q(v, a^n d)` is the sector at
    `v` opposite `v + C_(c_-)`, and `φ` maps it to the sector opposite `v + C_(c_-)` in `A`,
    which is `Q(v, c_+)`. Since `φ` fixes the ball,
    `Q(v, a^n d) ∩ B(v, R') = Q(v, c_+) ∩ B(v, R')`.
  - So `a^n d ∈ U` for all `n ≥ n_0` and all `d ∈ K`.
- **(PR3).** `a^-1` is strongly regular with the same translation apartment, translation
  `−τ`, and poles `(c_-, c_+)`. Apply (PR2) to it. ∎

## Lesson for general BH

In rank one, MIF comes from north–south dynamics on a boundary, with "distinct"
as the relation (Hull–Osin, Rybak). In higher rank, the right relation is
*opposition*, and strongly regular elements give north–south dynamics for it.

The proof uses only apartment geometry, namely opposite germs, common subsectors
and isometries fixing intersections. So the dynamical half of the higher-rank MIF
criterion is automatic for every group acting on a locally finite thick Euclidean
building. Uniform contraction was premise (PR2) of
`opposition-ping-pong-criterion-gives-mixed-identity-freeness`.

What remains for any such group, the Titz Mite–Witzel kernels in particular, is:
- density of pole pairs;
- *non-domesticity* of every nontrivial element at infinity, which is the
  higher-rank replacement for topological freeness.

With BFFHZ Theorem C, those two premises are all this route still needs to put a
higher-rank fp simple group in `B_A`. Membership there gives it every closure property
of BH.
