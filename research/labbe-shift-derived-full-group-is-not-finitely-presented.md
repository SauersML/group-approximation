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
refuted_by:
  - labbe-shift-derived-full-group-is-finitely-presented
---

**OPEN.** `D([[Z^2 ~ Omega_U]])` is not finitely presented.

**Why it matters.** It would settle `labbe-shift-derived-full-group-is-finitely-presented`, the
claim that now carries `hyperlinear-fp-infinite-simple-group` through the orbit certificate. It
would invalidate the three Labbé routes named above.

## Attempts

- **LEF.** Live: `labbe-not-fp-via-lef`. An infinite simple LEF group is not finitely presented.
  - The LEF question has its own claim, `labbe-shift-derived-full-group-is-lef`.
  - Its spatial crux is refuted (2026-09-13, unreviewed): finite models of quadratic Schreier growth that satisfy
    the short relators are trivial (`labbe-full-group-finite-small-growth-models-are-trivial`).
  - So a LEF refutation of finite presentation needs finite groups that act trivially whenever the growth is
    small.
- **Finite marked approximants of small growth.** Dead for the same reason. Any refutation through
  non-isolation needs infinite approximating marked groups, or finite ones none of whose nontrivial
  actions has quadratic growth up to scale `n`.
- **Infinitely generated homology.** Dead: `labbe-not-fp-via-infinitely-generated-homology`.
  `H_2 ≅ Z ⊕ T` with `T` finite, and all `H_j` are finitely generated
  (`labbe-shift-derived-full-group-homology-is-finitely-generated`).
- **Additive invariant-measure relation invariants.** Dead:
  `labbe-not-fp-via-mean-area-relation-invariant`. They factor through `N/[F,N]`, which is
  finitely generated.
- **Finite presentation forces finite type** (`zd-derived-full-group-fp-forces-finite-type`,
  unreviewed). Vacuous here, because `Omega_U` is a nearest-neighbour SFT.
  - It does sharpen the picture: among free minimal `Z^2`-subshifts, only SFTs can have finitely
    presented derived full groups, and `Omega_U` is one.
- **Matui's SFT-neighbourhood argument, spatial models, periodic approximations.** Dead as they
  stand. See `labbe-shift-derived-full-group-is-finitely-presented`, Attempts, and
  `minimal-free-sft-full-group-pattern-models-are-exact`.
- **What any refutation must look like.** Combine the vacuous finite-type theorem with
  `self-similar-tiling-full-groups-abelian-obstructions-vanish`. A refutation must be
  *nonabelian*, since no homology or additive relation invariant helps. It must also be *not
  spatial-legal*: it has to use colourings with illegal small windows, or non-spatial marked
  groups. LEF (`labbe-not-fp-via-lef`) is the recorded candidate of that shape.
- **Homology with nontrivial coefficients** (Bieri–Eckmann criterion for `FP_2`). Not attempted.
  Li's theorem reaches only coefficients pulled back from abelian covers.
- **Periodic quantum tilings (ex2-labbe-relation-climbing, 2026-09-13).** Live:
  `labbe-not-fp-via-periodic-quantum-tilings`.
  - A nonzero periodic operator-valued tiling of Labbé's tiles at every scale refutes finite
    presentation (`zd-derived-full-group-fp-excludes-periodic-quantum-tilings`, established,
    unreviewed). It needs no defect, no extended rule and no injectivity on balls, so it is a
    different mechanism from LEF.
  - The open input is `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`. By
    `periodic-quantum-tilings-refute-quantum-rigidity`, such a tiling must be contextual: no
    one-dimensional composition factor, and none of dimension 2 if `Omega_U` is wall-rigid.
- **Noncommuting operator families (ex2-labbe-relation-climbing, 2026-09-13).** Any noncommuting family
  (Q1)–(Q3) of Labbé's tiles at every scale, over a field of characteristic other than 3 and 5, refutes
  finite presentation (`zd-derived-full-group-fp-forces-quantum-rigidity`, established, unreviewed).
  Equivalently, a refutation of `labbe-wang-shift-crossed-product-is-finitely-presented` over `F_q`
  with `q` prime to 15 refutes the positive claim (read `labbe-crossed-product-fp-via-group-fp` in
  reverse). By `labbe-shift-is-wall-rigid` such a family must be contextual.
