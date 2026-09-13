---
rg: 2
id: labbe-shift-derived-full-group-is-not-finitely-presented
kind: claim
title: The derived subgroup of the topological full group of Labbé's Wang shift is not finitely presented
invalidates:
  - fp-simple-amenable-orbit-via-labbe-shift
  - fp-simple-irs-via-labbe-shift
  - fp-simple-amenable-via-labbe-shift-full-group
distinct_from:
  labbe-shift-derived-full-group-is-finitely-presented: That is the positive claim; this is its negation. When this claim is established it should be named in that claim's refuted_by, and it kills the three Labbé routes to the orbit-certificate, IRS and amenable roots.
  labbe-shift-derived-full-group-is-lef: That is local embeddability into finite groups, which would imply this claim; this is the negation of finite presentation itself, which could also follow from non-LEF mechanisms.
  labbe-shift-derived-full-group-homology-is-finitely-generated: That proves the homological obstruction to this claim vanishes; this is the negation itself, still open.
---

**OPEN.** `D([[Z^2 ~ Omega_U]])` is not finitely presented.

**Why it matters.** It would settle `labbe-shift-derived-full-group-is-finitely-presented`, the
claim that now carries `hyperlinear-fp-infinite-simple-group` through the orbit certificate. It
would invalidate the three Labbé routes named above.

## Attempts

- **LEF.** Live: `labbe-not-fp-via-lef`. An infinite simple LEF group is not finitely presented.
  The LEF question has its own claim and crux (`labbe-relator-shifts-carry-patch-rich-periodic-points`).
- **Infinitely generated homology.** Dead: `labbe-not-fp-via-infinitely-generated-homology`.
  `H_2 ≅ Z ⊕ T` with `T` finite, and all `H_j` are finitely generated
  (`labbe-shift-derived-full-group-homology-is-finitely-generated`).
- **Additive invariant-measure relation invariants.** Dead:
  `labbe-not-fp-via-mean-area-relation-invariant`. They factor through `N/[F,N]`, which is
  finitely generated.
- **Matui's SFT-neighbourhood argument, spatial models, periodic approximations.** Dead as they
  stand. See `labbe-shift-derived-full-group-is-finitely-presented`, Attempts, and
  `minimal-free-sft-full-group-pattern-models-are-exact`. Any refuting approximant must carry
  defects.
- **Homology with nontrivial coefficients** (Bieri–Eckmann criterion for `FP_2`). Not attempted.
  Li's theorem reaches only coefficients pulled back from abelian covers.
