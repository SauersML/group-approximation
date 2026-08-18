---
rg: 2
id: hs-normalization-via-robust-spectral-gap
kind: route
title: Close the (CCR)/(AC) residue by robust spectral gap and intertwiner transport
target: kt-centralizer-normalization-hs
requires: [el-r-polynomial-robust-spectral-gap, approximate-collapse-for-kt-compressor]
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

Gate outcomes (2026-08-18, second sweep pass — both executed):

- **Gate 0 PASSED, better than pass:** `(T;FD)_rob` needs no
  establishing — property (T) implies it unconditionally (DV
  Cor 7.7, §7, no lattice input), so the first `requires` is CLOSED
  BY CITATION (`el-r-polynomial-robust-spectral-gap-citation`).  The
  Becker–Lubotzky consistency worry resolves explicitly: DV print
  the `𝔽₂ × 𝔽₂` separation of hyperfinite from ordinary
  HS-stability, and the hyperfinite weakening is on the input class,
  so no contradiction.  The first sweep's line "establishing
  character rigidity or `(T;FD)^rob` … would close (AC)" is
  SUPERSEDED twice over: the property is free, and it closes only
  the uniformity gap, not (AC) proper.
- **Gate 1 PARTIAL POSITIVE (corrected after the §6 residual was
  closed by a full PDF read):** Peterson contains no answer to
  OP 6.2 and not the (CCR) shape — but he supplies (i) the printed
  (T)-interchange formula in the varying-dimension matrix ambient
  (proof of Prop 7.8) — cite it as precedent for
  `ccr-for-coordinate-collapsing-models`; (ii) the conjugated-family
  interchange under uniform weak spectral gap (𝒞_T remark) — the
  right template for any (CCR) drafting; (iii) Thm 5.2,
  coordinatewise deformations of (T) subfactors with factorial
  relative commutant are inner — a second intertwiner mechanism for
  the assembly, closer to the compressor picture than DV Lem 3.1
  (note its factorial-relative-commutant hypothesis is load-bearing);
  (iv) ∀∃-expressibility of relative-commutant statements for
  finitely presented (T) groups (Jekel remark) — a model-theoretic
  lever: such statements transfer along elementary equivalence, so
  (AC)-shaped facts proved for one ultraproduct transfer to
  elementarily equivalent ones.  FLAG: finite presentation of
  `EL_r(𝔽_q[x₁…x_d])` is now load-bearing twice (DV Def 7.5; the
  Jekel remark) — settle it before pulling either lever.
- **Gate 2 resolved by the above:** the direct attack on the
  `requires` is unnecessary; all remaining force goes to
  `approximate-collapse-for-kt-compressor` — via the assembly sketch
  above, or via the OP 6.2(b) conjugation-coherent-lift reduction.

Position after the gates: the route's spectral-gap half is in print
((T;FD)_rob for Γ free from (T); the `π ⊗ π̄` application template is
DV Lem 8.2; effective HS constants remain asserted-only, DV
Rem 7.11), and the sole open requirement is (AC) proper — one claim,
`approximate-collapse-for-kt-compressor`, on which the entire
rigidity route now rests.  The program remains ahead of the published
frontier (Alekseev–Thom OP 6.2, thirteen days old, unattempted).
