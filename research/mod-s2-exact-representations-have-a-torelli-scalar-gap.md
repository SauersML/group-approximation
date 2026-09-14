---
rg: 2
id: mod-s2-exact-representations-have-a-torelli-scalar-gap
kind: claim
title: Exact finite-dimensional representations of Mod(S_2) keep a separating twist uniformly far from cube-root scalars
artifacts:
  - research/artifacts/hl-nh-deligne-extension-2026-09-14.md
distinct_from:
  deligne-central-mark-hs-collapse: that is the one-word collapse over all almost representations of E_3, equivalently over almost representations of Mod(S_2) by (ST4); this restricts to genuine representations of Mod(S_2), so it is implied by that claim and is weaker.
  deligne-torelli-character-counts-separating-twists: its (ST5) excludes an exact cube-root scalar; this asks for a uniform normalized-HS distance from those scalars.
  mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors: that is the established dictionary and floor; this is the uniform gap itself.
---

**OPEN.** There is `delta_0 > 0` such that every finite-dimensional unitary representation `rho` of
`M = Mod(S_2)` and every separating Dehn twist `t_s` satisfy

```text
|| rho(t_s) - omega^(+-1) I ||_2  >=  delta_0 ,        omega = exp(2 pi i/3),
```

with `||.||_2` the normalized Hilbert–Schmidt norm. By
`mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors` (E1), this is equivalent to the
following: neither pulled-back Deligne sector trace `tau'_+`, `tau'_-` is a pointwise limit of normalized
characters of finite-dimensional unitary representations of `Mod(S_2)`.

**Position in the graph.**
- **Necessary for the genus-two route.** `deligne-central-mark-hs-collapse` implies this claim, by (E2)
  of the dictionary. A family of exact representations with vanishing defect would make `E_3` hyperlinear
  and refute `deligne-central-mark-hs-collapse`. It would not refute
  `deligne-stable-triple-cover-is-not-hyperlinear`, which may still hold at higher genus.
- **Sufficient under stability.** If `Mod(S_2)` is flexibly HS-stable, this claim is equivalent to
  non-hyperlinearity of `E_3`, by (E3).

## Attempts

- **Finite images.** (E4) gives `delta(rho) >= sqrt(3)/l(N)` for representations through `M/N`.
  - A finite-image counterexample family must use quotients where every short product of conjugate
    separating twists with exponent sum prime to 3 survives, i.e. `l(N) -> infinity`.
  - Whether `sup_N l(N) < infinity` is not decided. A bound would settle the finite-image part of this
    claim.
- **SU(2) quantum representations.** `research/artifacts/hl-nh-quantum-reps-2026-09-13.md` computes the
  exact spectra of separating twists up to level 400. The distance to scalars tends to 1. This is numerical
  evidence for one infinite-image family, not a proof for all levels, nor for other TQFTs.
- **No relative spectral gap (heuristic, unpinned).**
  - `Mod(S_2)` virtually surjects onto `Z`, through Birman–Hilden and a forgetful map onto `F_2`.
  - The image of the finite-index subgroup in `Sp_4(Z)` has property (T), hence finite abelianization. So
    every such surjection is nonzero on Torelli.
  - Hence `(Mod(S_2), I(S_2))` has no relative property (T). The gap can't come from relative-(T) rounding
    "almost Torelli-scalar => Torelli-scalar"; details in the artifact.
