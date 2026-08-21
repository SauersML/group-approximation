---
rg: 2
id: sl3-p3-pair-relative-commutant-collapse
kind: claim
title: Relative-commutant collapse for the p three SL3 pair
distinct_from:
  sl3-pair-relative-commutant-route: that is the p = 2 instance; this is the p = 3 instance where the candidate metaplectic flux is nontrivial, although the flatness and transport-identification seams remain open.
  sl5-pair-relative-commutant-collapse: that instance exists for the degree-2 cohomology infrastructure at rank four; this one exists because the Hilbert-symbol arithmetic decides the Lambda-exact face at p = 3 (mod 4), making it the lane's sharpest instance.
  lambda-exact-face-closes-at-p-three: that is the still-open proposed closure of the Lambda-exact face; this is the full collapse statement.
---

Let `Lambda = SL_3(Z)`, `Gamma = SL_3(Z[1/3])`,
`h = diag(3, 1, 1/3)`.  Claim `(RC3-p3)`: in every tracial matrix
ultraproduct `M` and every trace-preserving regular-trace
representation `pi` of `Gamma`,

```text
pi(SL_3(Z))' cap M = pi(SL_3(Z[1/3]))' cap M.               (RC3-p3)
```

Everything in the lane is prime-generic and instantiates verbatim:
co-density (CSP + superrigidity), commensuration with Schlichting
completion `PSL_3(Q_3)` (Howe--Moore, property (T)), the far-defect
formula, the lazy Hecke average with
`L = 3 . 4 . 13 = 156` and enemy fingerprint `1/4 + 1/624 =
157/624`, the one-commutator modulus, the character-face
compression, moment splitting, and the established reduction
`hnn-route-is-relative-commutant-collapse` for the goal group
`G_3' = < SL_3(Z[1/3]), t | [t, SL_3(Z)] = 1 >`.

What distinguishes this instance is a candidate nontrivial
metaplectic flux on oscillator bands. The prior claim that this
already closed the entire `Lambda`-exact face is invalidated by
`fixed-shift-invariance-does-not-force-flat-profile`: fixed-shift
invariance does not force a flat profile, and the parahoric-to-Weil
transport dictionary is also open. Thus `(RC3-p3)` still includes
both the spread `Lambda`-exact sector and the uniform-outlier sector.

## Attempts

- **The outlier sector is one of two remaining questions here.** Hyperfinite
  HS-stability of `SL_3(Z)` (in-graph, via character rigidity)
  corrects amenable-limit sequences; the regular-trace sequences
  are the non-amenable complement; the Dogon--Vigdorovich Question
  1.4 analogue at the lattice, with no central extension needed, is
  the outlier input. The other is the nonuniform Folner/spread sector
  left open by the failed fixed-shift-to-flat inference.
- **Falsification honesty.**  A uniform-outlier enemy for `p = 3`
  would be the first explicit non-correctable microstate family of
  a higher-rank lattice, itself a major structure theorem; the
  question remains two-sided.
