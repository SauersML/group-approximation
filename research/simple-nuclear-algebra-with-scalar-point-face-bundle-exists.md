---
rg: 2
id: simple-nuclear-algebra-with-scalar-point-face-bundle-exists
kind: claim
title: Some simple separable nuclear C*-algebra has a closed set of extreme traces whose W*-bundle has the scalar point property
distinct_from:
  pauli-tower-bundle-has-scalar-point-property: that is the non-simple Pauli tower, whose whole completion has the property; this asks for a simple algebra carrying it over a closed set of extreme traces.
  hilbert-cube-bauer-strict-comparison-indivisible-unit-exists: that asks for strict comparison, a Bauer simplex with Hilbert cube boundary and an indivisible unit; this asks only for simplicity and a closed face with the scalar point property, with no comparison hypothesis.
  toms-no-gamma-algebra-is-trivial-on-closed-bauer-faces: that shows Toms's simple no-Gamma algebra is trivial over every closed face; this asks for a simple algebra whose failure is visible over a closed face.
---

**OPEN.** There is a unital, simple, separable, nuclear, non-elementary C*-algebra `A` and a nonempty
closed `K ⊆ ∂_e T(A)` such that every self-adjoint element of the completion `M_K`
(`closed-extreme-trace-sets-give-r-fibre-w-star-bundles`) is scalar in some fibre over `K`.

**Why it matters.**
- `M_K` would be a nontrivial R-fibre bundle coming from a *simple* algebra.
- The algebra would lack uniform property Γ with the failure visible on a closed face, unlike Toms's example.
- For Toms–Winter this is the step between the non-simple Pauli tower and
  `hilbert-cube-bauer-strict-comparison-indivisible-unit-exists`. It would not settle Toms–Winter:
  under strict comparison, constant rank windows in `M_k(A)` divide the unit, so a comparison witness
  must exclude them in every amplification.

## Attempts

- **Induced point-evaluation blocks: dead as a small perturbation.**
  - Placing `a(x̃)` equivariantly into the Pauli bundle of stage `m` needs its holonomy orbit
    `⊕_{g ∈ G_m} a(x̃ g)`, with `G_m = (Z/2)^{2m}` acting through conjugation.
  - That is `4^m` copies of `M_{2^m}`, so a single point evaluation has weight about `4^m/(1 + 4^m)`.
- **Constant block ⊗ twisted factor: the period–index penalty** (constraint from lane
  `ex2-tw-hilbert-cube-boundary`).
  - A constant block `a(x)` must be tensored with a factor of the same Dixmier–Douady class. Its
    weight is then at least `ind/(1 + ind)`, with `ind = 2^m`, unless the main block is amplified.
  - A unital flat trivial amplification `M_t` adds `1 ⊗ diag(t_1, …, t_t)`, which is nowhere scalar. That kills
    the scalar point property, and also the rigidity `ε_0` of
    `bauer-strict-comparison-unit-divides-iff-atomless-element`.
  - Twisted amplifications under one projective cocycle push the forcing class from the adjoint Euler
    class to a Porteous-type class of the multiplicity-`ε_0 n` stratum, in degree about `ε_0² n²`
    (heuristic, per that lane).
- **Villadsen block maps: dead.** Equal-rank orthogonal blocks give central halving
  (`block-balanced-towers-have-central-halving`), hence trivial face bundles.
- **Crossed products by minimal homeomorphisms (heuristic).** Traces become invariant measures. A
  pointwise scalar point on a null set is invisible, so the obstruction is lost.
- **Braided rotation doubling: open, and the most promising design.**
  - **The map.** `φ(a)(z, ỹ) = diag(a∘h_ỹ(z), a∘h_{−ỹ}(z))`, with `h_ỹ` isometries of `Z_m` that lift to the
    principal bundle.
    - The antipodal loop of a new sphere coordinate swaps the blocks (holonomy `X`). A sign coordinate
      gives holonomy `Z`.
    - So the multiplicity space is itself the new Pauli factor. There is one projective cocycle and no weight
      penalty.
  - **Why the obstruction should transfer (heuristic).**
    - Exact relative commutants of `φ(A_m)` are block-diagonal on coincidence classes, so they lie
      inside the tail bundle `M_{2^r}`.
    - Separating blocks with partitions of unity makes approximately central elements approximately
      block-diagonal where the blocks are far apart. Frames at nearby points are nearly equal.
    - So soft halvings would give soft halvings of the Pauli tail, which Theorem A forbids.
    - The partial-trace estimate across nearly coinciding blocks was not written out.
  - **Coincidences and simplicity.**
    - If `h_{−ỹ}^{-1} h_ỹ` is an odd function into a vector-like chart, Borsuk–Ulam forces coincidences.
    - Coinciding blocks at every stage leave a nonempty vanishing set `F_m` for a small positive element,
      and then the limit is not simple.
    - A fixed-point-free involutive isometry `ι` (multiplication by `i` on `RP^{2k+1}`; the tower allows
      odd `d_j ≥ 2^{j−1}`) with `h_{−ỹ} = h_ỹ ∘ ι` avoids coincidences.
    - Simplicity then needs the `2^r` composite rotations to form nets of `Z_n` at every point, which
      needs non-commuting `ι_k`.
  - **Not examined.**
    - Whether a closed set of branch traces is extreme, given the Poulsen obstructions of
      `toms-doubling-ah-trace-simplex-is-poulsen`.
    - Whether the equivariant maps `S^d → Isom_0` with `h(−ỹ) = h(ỹ)ι` exist in the needed dimensions.
