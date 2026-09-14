# sk-exact-banded, part 2 (2026-09-14): exactness passes down to the limit subsystem

Lane sk-exact-banded. Part 1: `research/artifacts/sk-exact-banded-2026-09-14-part1.md`. The question whether `G_X` is exact stays OPEN. This part proves that all the difficulty sits in the recurrent (minimal) subsystems.

## 1. Result (established, unreviewed)
Claim `subshift-gl-exactness-reduces-to-limit-subsystem`, route `subshift-gl-exactness-reduces-to-limit-subsystem-proof`.
- **Setting:** `Y` is a subshift and `Z ⊆ Y` is closed and invariant, with both limit sets of every point outside `Z` contained in `Z`.
- **Theorem:** a finitely generated `Γ ≤ GL_m(LC(Y,F_2) ⋊ Z)` is exact whenever its image over `Z` is. The congruence kernel is locally finite, because the complement ideal is ultramatricial.
- **Corollaries:**
  - (a) Filtrations ending in finitely many periodic orbits give exact groups, via Guentner–Tessera–Yu for commutative-ring linear groups.
  - (b) Every finitely generated group of banded matrices over `F_2` whose coefficient functions are eventually periodic in both directions is exact.
  - (c) If the bottom of a filtration is an infinite minimal subshift `X`, exactness reduces to the open question for `GL_m(R_X)`.

## 2. Inputs
- **On main, reviewed:** `biasymptotic-subshift-complement-ideal-is-ultramatricial` and `ultramatricial-ideals-have-elementary-congruence-kernels` (both PASS by sk-verify-5).
- **On main, part 1:** `banded-matrix-groups-are-subshift-crossed-product-groups` (unreviewed).
- **New import nodes:**
  - `exact-groups-are-closed-under-extensions` (Kirchberg–Wassermann, Documenta Math. 4 (1999) 513–558). Abstract read at source in the published PDF: "It is shown that the class of exact groups, as defined in a previous paper, is closed under various operations, such as passing to a closed subgroup and taking extensions."
  - `commutative-ring-linear-groups-have-property-a` (Guentner–Tessera–Yu, GGD 7 (2013) p. 378). The verbatim quotes were already recorded by sk-exact-gx.

## 3. What this says about the problem
- Together with part 1, exactness of finitely generated groups of banded matrices over `F_2` reduces, along any filtration by limit sets, to the bottom subsystem.
- When the bottom is a finite union of periodic orbits, the answer is yes. When it is an infinite minimal subshift, the question is exactly the open one for `GL_m(R_X)`.
- So the open problem is concentrated in minimal aperiodic dynamics, as expected. By part 1 it is invariant under Kakutani equivalence and rank.
- **Not covered:** subshifts whose non-minimal orbits accumulate on recurrent non-minimal sets without a filtration of this kind. There the complement ideal of the natural subsystem need not be ultramatricial: `biasymptotic-subshift-complement-ideal-is-ultramatricial` notes that corners meeting recurrent orbits outside the subsystem are not locally finite.

## 4. Next targets
- **(P-b)** Property A of the bounded-width fibres `Q_r` in `G_X` for minimal `X`. The obstruction to a direct asdim-0 argument is recorded in part 1 §4.
- **N3** Can a residually finite non-exact group act faithfully by banded matrices over a finite field? By Corollary (c), such a representation must use recurrent coefficient dynamics.
