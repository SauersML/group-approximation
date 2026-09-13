---
rg: 2
id: sl3-polynomial-finite-index-z-extension-center-survives
kind: claim
title: A finite-index subgroup of SL_3(F_q[t]) has a central Z-extension with finite abelianization whose centre survives at unbounded orders in finite quotients
distinct_from:
  sl3-polynomial-covers-have-extra-finite-quotients: that is the profinite premise for the truncated finitely presented covers of SL_3(F_q[t]); this is the premise for a central Z-extension of a finite-index subgroup, the cohomological route.
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that records the failure model, a Kazhdan central Z-extension whose centre is invisible in finite quotients; this asks for the opposite behaviour at a congruence subgroup of SL_3(F_q[t]).
---

**OPEN.** For some prime power `q`, there are:
- a finite-index subgroup `Δ` of `SL_3(F_q[t])`;
- a central extension `1 -> Z = ⟨z⟩ -> Δ~ -> Δ -> 1`, where `Δ~` has finite abelianization;

such that the order of the image of `z` in finite quotients of `Δ~` is unbounded.

**Consequence if true.**
- `Δ~` is Kazhdan (`bdhv-central-extension-property-t`).
- Regular representations of finite quotients cut down to central characters `e^(2πi/n_k)`,
  `n_k -> ∞`, satisfy (KC1) with `Fix_(⟨z⟩) = 0`. So `Δ` is not flexibly HS-stable
  (`kazhdan-cover-models-round-iff-kernel-fixed-mass-one`).
- Hence neither is `SL_3(F_q[t])`, nor the rank-3 Kun--Thom vertex
  (`el-r-vertex-instability-via-congruence-central-extension`).

## Attempts

- **A real class is necessary (elementary).**
  - If the image of the extension class in `H^2(Δ;R)` vanishes, then a real cochain `f` with
    `δf = c` gives a homomorphism `Δ~ -> R` with `z -> 1`. Then `Δ~` has infinite abelianization.
  - So `H^2(Δ;R) ≠ 0` is needed.
- **`Δ` must be proper (not source-verified).**
  - `SL_3(F_q[t])` acts on the Bruhat--Tits building of `SL_3(F_q((1/t)))` with finite
    stabilizers and a sector as strict fundamental domain (Soulé). So its real cohomology vanishes
    in positive degrees, and `Δ` must be a proper subgroup.
  - For congruence subgroups, degree-two real cohomology is expected from cuspidal automorphic
    forms that are Steinberg at `∞`, i.e. the top degree of the 2-dimensional building, following
    Harder's cohomology of S-arithmetic groups over function fields. Not checked.
- **Real classes exist at explicit levels (2026-09-13).** See
  `sl3-polynomial-congruence-subgroups-have-large-b2`, which is conditional on Soulé's
  strict fundamental domain.
  - `b_2(Γ(t^2)) = 927` for `q = 2` and `132920` for `q = 3`. Levels of degree 2 and 3 have
    thousands of real degree-two classes, and level `t` has none.
  - Integral classes with nonzero real image exist, so central `Z`-extensions of `Γ(f)` with
    finite abelianization exist.
  - The first requirement of this claim therefore holds at those levels. What is left is survival
    of the centre in finite quotients.
- **Survival can only happen at `p`-power orders (heuristic; assumes the congruence subgroup
  property, not verified).**
  - If `z` has order `n` in a finite quotient, the class mod `n` is inflated from a finite
    congruence quotient of `Δ`.
  - Such quotients are extensions of products of `SL_3` over finite fields by finite `p`-groups
    (`p = char F_q`). For primes `ℓ ≠ p`, their `H^2(-;Z/ℓ^k)` is bounded by Schur multipliers
    of the simple factors.
  - So the `ℓ`-part of the order of `z` stays bounded, and only `p`-power orders can grow.
  - The needed detection is therefore a goodness-type statement for the pro-`p` congruence
    kernels in degree 2.
- **Failure model.** For `Sp_(2g)(Z)`, the Deligne cover has finite abelianization and (T), but
  the centre has bounded order in finite quotients (`deligne-universal-cover-lattice-is-non-rf-kazhdan`).
  The analogous non-detection is the main risk here.
- **Harder's theorem and the Laurent host (2026-09-13).**
  - `harder-function-field-s-arithmetic-cohomology-vanishing` (with `S = {∞}`) confirms the
    expectation in the second bullet: congruence subgroups of `SL_3(F_q[t])` have real cohomology
    only in degrees 0 and 2, and `b_2` is the multiplicity of the Steinberg representation at `∞`.
  - The consequence of this claim stops at `SL_3(F_q[t])` and the Kun--Thom vertex. Flexible
    stability does not pass from a subgroup of infinite index to the host, so it does not reach
    `SL_3(F_q[t,1/t])`.
  - There the analogous route is void. Every congruence subgroup of the Laurent group has no real
    `H^2`, so a central Kazhdan cover has finite kernel
    (`laurent-sl3-central-covers-never-witness-instability`). No nonzero real class of `Γ(f)`
    extends to the Laurent congruence subgroup `A(f)`
    (`laurent-sl3-real-cohomology-from-chamber-quotient`).
