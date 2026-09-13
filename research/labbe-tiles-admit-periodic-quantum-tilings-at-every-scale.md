---
rg: 2
id: labbe-tiles-admit-periodic-quantum-tilings-at-every-scale
kind: claim
title: Labbé's 19 Wang tiles admit a nonzero periodic quantum tiling at every scale
distinct_from:
  labbe-wang-shift-crossed-product-is-finitely-presented: that asks whether every operator-valued local tiling commutes; this asks for periodic finite-dimensional tilings at every scale, which would refute both that claim and finite presentation of the derived full group.
  labbe-relator-shifts-carry-patch-rich-periodic-points: that seeks classical periodic colourings with defects on which extended rules satisfy short relators; this seeks operator-valued periodic families that satisfy the local tiling rules exactly, with no defect.
artifacts:
  - research/artifacts/labbe-periodic-quantum-tilings-obstruct-fp-2026-09-13.md
---

**OPEN.** For every `D >= 1` there exist:
- a field `k`, a nonzero finite-dimensional `k`-space `W` and a finite-index lattice `Λ ≤ Z^2`;
- idempotents `E_a(z) ∈ End_k(W)`, for `a` among the 19 tiles of `Omega_U` and `z ∈ Z^2`, with
  `E_a(z + λ) = E_a(z)` for `λ ∈ Λ`;

satisfying (Q1)–(Q3) of `sft-crossed-product-fp-iff-quantum-rigid` for `Omega_U` at scale `D`.

**Payoff.**
- By `zd-derived-full-group-fp-excludes-periodic-quantum-tilings`, `D([[Omega_U]])` would not be
  finitely presented (route `labbe-not-fp-via-periodic-quantum-tilings`).
- By `periodic-quantum-tilings-refute-quantum-rigidity`, the crossed product
  `LC(Omega_U, k) ⋊ Z^2` would not be finitely presented either.

**Model test.** For a periodic SFT, `W = k` with a classical periodic tiling satisfies the statement.
`W = 0` is excluded. For `Omega_U` every classical family fails, since it would be a periodic legal
tiling.

## Attempts

- **Classical families.** Dead. If all `E_a(z)` commute, a joint eigenvector reads off a legal
  configuration invariant under `Λ`, and `Omega_U` is aperiodic (`minimal-aperiodic-wang-shift-exists`).
- **One-dimensional composition factors.** Dead. A one-dimensional `C_D`-composition factor of a
  finite-dimensional module reads off a legal periodic configuration
  (`periodic-quantum-tilings-refute-quantum-rigidity`, item 1).
- **Two-dimensional composition factors.** Dead if `Omega_U` is `D`-wall-rigid
  (`sft-wall-rigidity-iff-idempotent-commutator-ideal`; item 3 of the periodic node). Wall rigidity of
  `Omega_U` is itself only heuristic: the fibre argument recorded in
  `labbe-wang-shift-crossed-product-is-finitely-presented`, Attempts.
- **Contextual families.** Open. What remains are noncommuting composition factors of dimension
  `>= 3`. Operator solutions of contextual constraint systems (magic-square type) show that such
  behaviour exists for local constraint systems; none has been built for Wang tiles here.
- **Scale.** Open. A search at `D = 1` or `2` over `F_2` or `F_3` with small `W` and `Λ` has not been
  run. It could only give evidence, since the route needs every large `D`.
