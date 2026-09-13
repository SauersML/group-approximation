---
rg: 2
id: abelian-isometry-groups-of-h2-are-not-cobounded-proof
kind: route
title: Abelian isometry groups of H^2 lie in centralizers of one element, whose orbits are curves
target: abelian-isometry-groups-of-h2-are-not-cobounded
requires: []
---

Replace `A` by its image, an abelian subgroup of `Isom(H^2)`. Use the upper half-plane,
`Isom^+(H^2) = PSL_2(R)`.

**Step 0 (orientation).** `A^+ = A ∩ PSL_2(R)` has index at most 2. If `σ ∈ A \ A^+` and
`x ∈ H^2`, then for `a ∈ A^+` we have `d(aσx, ax) = d(σx, x) =: c`, so
`A·x ⊆ N_c(A^+·x)`. Hence if `A` has a coarsely dense orbit, so does `A^+`.
If `A^+ = 1`, orbits of `A` have at most two points, and `H^2` is unbounded. Otherwise fix
`g ∈ A^+`, `g ≠ 1`. Since `A^+` is abelian, `A^+ ⊆ C(g)`, the centralizer of `g` in `PSL_2(R)`.

**Step 1 (centralizers).** Lift `g` to `G ∈ SL_2(R)`, `G ≠ ±I`. An element `±H` centralizes
`±G` iff `HGH^{-1} = ±G`. The sign `−` needs `tr G = −tr G`, so `tr G = 0`, i.e. `G` is
conjugate to `J = [[0,1],[−1,0]]`; but `HJ = −JH` forces `H = [[a,b],[b,−a]]` with
`det H = −a²−b² < 0`, impossible. So `C(g)` is the image of the centralizer of `G` in `SL_2(R)`.
- `|tr G| < 2` (elliptic): up to conjugacy `G = R_θ` (rotation matrix), `θ ∉ πZ`, with distinct
  eigenvalues `e^{±iθ}`; its centralizer in `M_2(R)` is `R[G]`, and `R[G] ∩ SL_2(R) = SO(2)`.
  So `C(g)` fixes the point `i`.
- `|tr G| > 2` (hyperbolic): up to conjugacy `G = diag(λ, λ^{-1})`, `λ > 1`; the centralizer is
  the diagonal group, so `C(g) = {z ↦ μz : μ > 0}`.
- `|tr G| = 2`, `G ≠ ±I` (parabolic): up to conjugacy `G = ±[[1,s_0],[0,1]]`, `s_0 ≠ 0`;
  `[[a,b],[c,d]]` commutes with it iff `c = 0` and `a = d`, so `C(g) = {z ↦ z + s : s ∈ R}`.

**Step 2 (orbits are not coarsely dense).** Fix `x ∈ H^2`.
- Elliptic: `A^+·x` lies on the hyperbolic circle about `i` through `x`, a bounded set.
- Hyperbolic: `A^+·x ⊆ {μx : μ > 0}`, a Euclidean ray from `0`, which is an equidistant curve
  of the geodesic `ℓ = iR_{>0}`: all its points are at the same distance `D` from `ℓ`. For
  `y ∈ H^2`, `d(y, A^+·x) ≥ d(y, ℓ) − D`, and `d(y, ℓ)` is unbounded on `H^2`
  (take `y = e^{iψ}` with `ψ → 0`).
- Parabolic: `A^+·x ⊆ {Im z = Im x}`. The function `b(z) = log Im z` is 1-Lipschitz
  (`ds = |dz|/Im z ≥ |d Im z|/Im z`). So `d(y, A^+·x) ≥ |log Im y − log Im x|`, unbounded.

In all cases `A^+`, hence `A`, has no coarsely dense orbit. ∎

Model test: `Z[1/2] ⋊ Z` acting on `H^2` by `z ↦ 2^n z + m/2^k` is solvable and cobounded,
so "abelian" cannot be weakened to "solvable".
