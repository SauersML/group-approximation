---
rg: 2
id: hs-normalization-via-robust-spectral-gap
kind: route
title: Close the (CCR)/(AC) residue by robust spectral gap and intertwiner transport
target: kt-centralizer-normalization-hs
requires: [el-r-polynomial-robust-spectral-gap]
artifacts:
  - research/el-r-polynomial-robust-spectral-gap.md
---

# Close the (CCR)/(AC) residue by robust spectral gap

The 2026-08-18 sweep's consolidated verdict: one transportable proof
mechanism exists for the non-liftable case of (AC), namely uniform
spectral gap for ASYMPTOTIC finite-dimensional representations
(`(T;FD)^rob`) of `Γ = EL_r(𝔽_q[x₁…x_d])`, consumed through the
published machinery:

1. `(T;FD)^rob` (or character rigidity) for Γ — the `requires`, open,
   `el-r-polynomial-robust-spectral-gap`;
2. Dogon–Vigdorovich intertwiner transport (arXiv:2506.20843,
   Lem 3.1 / Prop 3.3): closeness on generators yields exact
   intertwiners with uniformly bounded operator norm — the tool that
   relates `σ(Γ)'` to `σ(Λ)' = σ(t)σ(Γ)'σ(t)^*` inside the
   ultraproduct without any coordinate homomorphisms;
3. de la Salle's quantitative spectral-gap Poincaré inequality
   (arXiv:2204.07084, Lem 2.2) as the finite-stage engine replacing
   the per-coordinate Kazhdan inequality that genuine coordinates
   supplied in `ccr-for-coordinate-collapsing-models-proof`;
4. the congruence collapse `π(Γ) ⊆ π(Λ)` (E-normality,
   `compressor-coset-two-point-exact`) at whatever finite stages the
   robust gap makes available.

Assembly sketch (to be made precise by the campaign): robust gap
turns the exact `Λ`-invariance of `x ∈ σ(Λ)'` into quantitative
invariance under approximate images at finite stages; intertwiner
transport replaces the missing `π_n(γ) = π_n(λ_n)` identification;
the collapse supplies the identification's content.  This is the
unitary-side substitute for Kun–Thom 4.1's cluster-groupoid medians,
which a full census confirmed are structurally non-transportable (no
set is acted on).

Gates before any assembly work, in order:

- **Gate 0 (consistency):** verify Dogon–Vigdorovich's definition of
  hyperfinite HS-stability and check that `(T;FD)^rob` does NOT imply
  ordinary HS-stability for residually finite (T) groups — else
  Becker–Lubotzky (arXiv:1809.00632) refutes the `requires` outright
  and this route is dead on arrival.  Hours, not months; do it first.
- **Gate 1:** read Peterson arXiv:2605.16669 in full — the sweep's
  one flagged gap, and the likeliest place partial answers to
  Alekseev–Thom OP 6.2 are hiding.
- **Gate 2:** decide whether to attack `(T;FD)^rob` for Γ directly
  (Dogon–Vigdorovich's central-extension machine has never been run
  on `1 → K₂ → St → EL → 1` over polynomial rings) or via the
  OP 6.2(b) conjugation-coherent-lift reduction recorded in the
  `requires` node.

Position honestly stated: this route rests on an open `requires` that
no one has attempted, for a group outside every class the published
results cover.  It is nevertheless the only mechanism-backed route to
the residue in the literature as of 2026-08-18, and it is new — the
program is ahead of the published frontier here (the ambient
unitary question is Alekseev–Thom OP 6.2, thirteen days old).
