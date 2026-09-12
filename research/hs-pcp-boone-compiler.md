---
rg: 2
id: hs-pcp-boone-compiler
kind: claim
title: PCP-ize the Boone halting word with a runtime-independent normalized-HS gap
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
  - research/artifacts/self-similar-dimension-pressure-map-2026-08-20.md
  - research/artifacts/conjugacy-addressed-machine-groupification-audit-2026-08-20.md
  - research/artifacts/adversarial-dimension-matched-hs-pcp-synthesis-2026-08-20.md
distinct_from:
  boone-commutator-criterion-for-halting: ordinary Boone gives an exact equality after a derivation whose area depends on runtime; this asks for uniform approximate soundness independent of runtime.
  robust-locally-satisfiable-relator-code: that asks for one finite redundant relator menu suitable for sparsification; this asks for a uniform MACHINE-TO-MARKED-GROUP compiler with the nonhalting/halting orientation needed by Kleene self-reference.
  perfect-lcs-gap-implies-nonhyperlinear: that consumes one perfect LCS gap; this asks for a robust group compiler which would manufacture the needed fixed witness directly.
---

Construct a total computable map

```text
M |-> (G_M=<S_M|R_M>, w_M)
```

and universal computable rational constants `delta>0` and
`0<alpha<sqrt(2)` satisfying

```text
M does not halt  =>  w_M != 1 in G_M,                              (HPB1)

M halts          =>  Def_R_M(U)<delta
                     implies ||w_M(U)-1||_2<=alpha                 (HPB2)
```

for every finite-dimensional unitary tuple `U`, with no dependence of the
constants on the halting time.

This is the exact missing premise of
`kleene-self-destroying-microstate-lemma`.  The existing
`boone-commutator-criterion-for-halting` supplies the logical biconditional but
not `(HPB2)`: naive relation telescoping costs the area of the computation.

## Attempts

- Use `kleene-mipco-self-destroying-game` as the constant-gap verifier source.
- Use `odd-selector-priority-decoding` when lowering verifier control to LCS
  syntax.  It eliminates selector-overlap suppression; only consistency
  between local decoded contexts remains on that side of the compiler.
- Exactify a fixed finite-group CPU and select a positive-density irreducible
  sector; `finite-predicate-signed-permutation-sector` supplies arbitrary
  nonlinear local rules inside such an exact sector.
- Use `multiplicity-pi-turing-tape` and
  `two-generator-amitsur-levitzki-dimension-oracle` to detect the finite
  multiplicity without supplying its dimension to the program.
- Do not replace that discrete multiplicity pressure by a bare cyclic
  character orbit.  `cyclic-character-orbit-pressure-has-vanishing-hs-gap`
  gives scalar near-models whose mark tends to maximal separation while the
  orbit relation defect is only `O(1/p)`.
- Make the terminal failure a fixed holonomy or use
  `conjugacy-compressed-dimension-trigger` so the last flag itself has no
  runtime-dependent norm loss.
- More generally, literal conjugate copies of a finite menu of prototype
  checks have exactly zero address-length loss.  The remaining machine
  theorem is therefore not local transport but global decoding: it must
  combine conjugacy-addressed checks with constant-soundness consistency of
  the cell names.  `stabilizer-generator-control-has-unbounded-address-loss`
  shows why an orbit tape plus finitely many stabilizer-generator relations
  does not provide that consistency by itself.
- Prove the still-missing semantic transport estimate from the triggered
  finite control to the fixed mark with a universal constant.  Escaping the
  selected sector must pay through positive-density carrier overlap and fixed
  holonomy, not through a dimension-dependent rank count.
- The alternative `hs-pcp-boone-via-supercritical-clifford-trigger` route
  sharpens the dimension-pressure idea to the required same-model inequality
  `d>=F(d)>d`.  Slofstra's profile construction proves only that the least
  dimension grows rapidly as defect shrinks; finite growth alone is compatible
  with hyperlinearity.

The mandatory falsification test is the runtime: a proof yielding
`C T(M) Def(U)` or a polynomial whose coefficient/degree loss grows with the
detected dimension does not establish `(HPB2)`.

Equivalently, a dimension-matched backend may target the carrier estimate

```text
(1/4)||w_M(U)-1||_2^2
  <= 2^(-N(D)) + C_M Def_(R_M)(U)^2,
```

where `M` halts with output `D` and `C_M` is computable from the source before
the fixed-point search begins.  This is sufficient for the
`instance-modulated-kleene-microstate-diagonal`; any dependence of the defect
coefficient on `D`, `N(D)` or halting time returns to the amplification-
envelope obstruction.
