---
rg: 2
id: hilbert-cube-bauer-strict-comparison-indivisible-unit-exists
kind: claim
title: A nuclear strict-comparison algebra with Bauer Hilbert cube boundary and indivisible unit exists
distinct_from:
  stw27-strict-comparison-non-pure-algebra-exists: that asks for any nuclear strict-comparison algebra that is not pure; this fixes a Bauer simplex with Hilbert cube boundary and asks for failure at the unit.
  ash-strict-comparison-rank-gap-algebra-exists: that asks for an ASH algebra with a rank gap and no tracial restriction; this fixes the tracial boundary and allows any building blocks.
  nontrivial-w-star-bundle-with-r-fibres-exists: that asks for a nontrivial hyperfinite W*-bundle with no C*-algebra and no comparison; a witness here gives one over the Hilbert cube, with strict comparison on top.
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-part4-2026-09-13.md
---

**OPEN.** There is a unital, simple, separable, nuclear, non-elementary
C*-algebra `A` with strict comparison of positive elements, whose trace simplex is
Bauer with extreme boundary homeomorphic to the Hilbert cube `Q`, and whose unit is
not tracially `N`-divisible for some `N`.

Such an `A` is not pure (`bauer-strict-comparison-pure-iff-divisible-unit`), so it
refutes STW XXVII(1) and Toms–Winter (route
`stw27-counterexample-from-hilbert-cube-indivisible-unit`). The exact non-nuclear
analogue would refute purity under strict comparison for exact algebras on the
same locus; it is not recorded as a separate claim.

**What a witness must satisfy** (each item names its source on main).
- **Confinement.** `ℓ_A(ω) ≤ 2^{−c/ω}` for some `c > 0` and all small `ω`: local
  divisions of matrix size `N` live on sets of `ρ`-diameter about `2^{−cN}`
  (`bauer-unit-division-metric-order-criterion`, unreviewed). At a fixed defect `κ_0` the
  confinement is exponential in `N` alone: `ℓ_A(N, κ_0) ≤ 16 · 2^{−κ_0 N}`
  (`bauer-unit-division-defect-uniform-criterion`, unreviewed).
- **Nontrivial bundle.** Its strict closure is a nontrivial R-fibre W*-bundle over
  `Q`. A trivial bundle gives uniform Gamma
  (`bauer-uniform-gamma-iff-trivial-tracial-bundle`), and uniform Gamma with strict
  comparison gives `Z`-stability (`uniform-gamma-algebras-satisfy-toms-winter`).
  So a witness also answers BBSTWW Question 3.14, and the negative side is at least
  as hard as `nontrivial-w-star-bundle-with-r-fibres-exists`.
- **Tracial eigenvalue rigidity.** Some `ε_0 > 0` works for every self-adjoint `h ∈ A`: at some
  extreme trace `λ`, `π_λ(h)` has an eigenprojection of trace at least `ε_0`
  (`bauer-strict-comparison-unit-divides-iff-atomless-element`, unreviewed).
  - In particular `A` has no unital zero-dimensional `C(Y)` on which extreme traces are atomless, so
    no Cantor Cartan subalgebra of that kind (`zero-dimensional-atomless-diagonal-divides-unit`).
  - Heuristically, in (sub)homogeneous blocks of size `n` over `d`-dimensional spectra this needs
    `d ≳ ε_0² n²`: multiplicity `ε_0 n` is a stratum of codimension about `ε_0² n²`.
- **No projection certificate.** Its tracial ultrapower compares projections by
  limit traces in every matrix size
  (`strict-comparison-compares-ultrapower-projections`, reviewer PASS). So
  Villadsen Euler-class gaps and Thom–Porteous degeneracy loci cannot certify it.
  The obstruction must be an existence gap.
- **Class exclusions.**
  - Not AH (`simple-ah-strict-comparison-is-z-stable`).
  - With tracially locally finite nuclear dimension, stable rank at least 2: stable
    rank one gives uniform Gamma (Vaccaro, arXiv:2604.24682v2, Theorem B, as recorded
    on `research/artifacts/tw-support-gap-crux-2026-09-12.md`).
  - Not an ASH algebra of subquadratic dimension growth (arXiv:2607.23817, as
    recorded in `research/artifacts/ex-open-status-2026-09-12.md`; not re-read by this
    lane).

## Attempts

- **Product towers with characteristic classes (heuristic).** Let the unit bundle
  over `Π_{i≤m} S²` carry coordinate Hopf summands.
  - The mod-`ℓ` Frobenius count (`stw27-coordinate-euler-slack-obstructs-compact-dividers`)
    makes an `ℓ`-division with defect rank `ρ` impossible once more than `ρ` twisted
    coordinates are left unpinned.
  - Confinement pinning `cN` coordinates at defect `δ` needs about `cN` twisted
    coordinates against a unit rank `R` with `δR ≲ cN`. So the dimension-to-rank ratio
    stays bounded below at every precision.
  - In homogeneous blocks that ratio is what breaks comparison (Villadsen, Toms), and
    AH witnesses are excluded anyway. Linear pinning from finite-stage topology needs
    a mechanism that keeps comparison while dimension is comparable to rank. None is
    known; `ash-strict-comparison-rank-gap-algebra-exists` records the same tension.
- **Tensor towers.** For `⊗_k End(W_k)` over `Π_k Y_k`, divisions pin only as many
  coordinates as the tail ranks require, logarithmically many in `N` when ranks grow
  geometrically. These algebras are not simple. Lane `ex2-tw-unsplittable-tails` owns
  `some-tensor-tower-has-unsplittable-tails`.
- **Doubling versus Bauer.** Toms-style propagation uses two independent copies of
  the old base, which averages point traces and destroys closedness of the extreme
  boundary (`research/artifacts/tw-hilbert-cube-projection-invariant-2026-09-12.md`,
  Section 3). A witness needs an obstruction that propagates without averaging.
