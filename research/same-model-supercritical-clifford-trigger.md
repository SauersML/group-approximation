---
rg: 2
id: same-model-supercritical-clifford-trigger
kind: claim
title: Compile a halting computation into a supercritical Clifford challenge inside the same matrix model
artifacts:
  - research/artifacts/self-similar-dimension-pressure-map-2026-08-20.md
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
distinct_from:
  slofstra-subexponential-hyperlinear-profile: that forces the minimum dimension to grow as defect decreases; this asks the candidate d-dimensional model to generate, inside itself, a certified Clifford system requiring dimension strictly greater than d.
  two-generator-amitsur-levitzki-dimension-oracle: that detects the finite multiplicity index exactly in an exact matrix algebra; this must robustly turn the detected index into a dimension contradiction with constant normalized-HS loss.
  constant-hs-sound-self-detecting-tape-groupification: that states the full finite CPU/tape groupification hardware; this isolates the intended same-model dimension inequality which that hardware is supposed to realize.
  projective-holonomy-rank-forces-exponential-multiplicity: that proves exact rank-`2r` packet holonomy forces a `2^r` divisor on external multiplicity; this must robustly activate such rank beyond the multiplicity detected in the current approximate model.
---

Construct a uniform machine-indexed finite group gadget with universal
constants `delta>0`, `0<alpha<sqrt(2)`, and the following halting soundness
property.

For every `d`-dimensional unitary tuple `U` satisfying

```text
Def(U)<delta,                  ||w(U)-1||_2>alpha,
```

the gadget, **inside the same `C^d`**, identifies a positive-density invariant
corner and an `epsilon_Cl`-homomorphism from the entire finite Clifford group
`C(n(U))` on that corner, with `epsilon_Cl` bounded by a universal constant
times `Def(U)`.  Then `robust-clifford-capacity-bound` must imply

```text
dimension(corner) >= 2^(floor(n(U)/2)-1) > d.             (SMC1)
```

The strict last inequality is certified by the computation after detecting
the model's finite multiplicity; it is not an external choice of a larger
follow-up model.  Thus `(SMC1)` contradicts the existence of `U` and yields
the uniform marked-word collapse required in the halting case.

All losses—carrier extraction, instruction simulation, Clifford
anticommutation, and return to the fixed marked word—must be bounded by a
constant multiple of `Def(U)` independent of `d`, `n(U)`, and runtime.
Without that uniformity this reduces to an ordinary rapidly growing
hyperlinear profile, which hyperlinearity permits.

This is the literal target

```text
d >= F(d) > d
```

rather than `d_next >= F(d)`: choosing a larger approximation must activate a
larger incompatible challenge in that very approximation.

## Attempts

- **Slofstra addressing without diagonalization stops at a finite profile.**
  The shift and HNN square map address `n` Clifford generators by words of
  polylogarithmic length, but choosing `n` from the external defect tolerance
  only proves a large finite lower bound on `d`.
- **Amitsur--Levitzki detects capacity but loses uniformity.**  On an exact
  `M_k` multiplicity tape, `p_k=0` supplies an endogenous stopping index.
  Directly evaluating or telescoping `p_k` has degree and coefficient mass
  growing with `k`, so it cannot trigger a fixed HS gap.
- **Active attack.**  Feed the first vanishing identity into a constant-gap
  local verifier and use a positive-density finite-group carrier to request
  `n(k)>2 log_2 d+O(1)` Clifford checks in parallel.  The unresolved step is a
  finite group-word compiler that turns those local checks into an
  all-pairs approximate homomorphism and returns the triggered failure to the
  mark with constants independent of `k` and verifier runtime; this is the same
  quantitative hardware isolated in
  `constant-hs-sound-self-detecting-tape-groupification`.
- **Equivalent packet-holonomy formulation.**  It is enough to make the
  triggered computation activate a binary projective holonomy form of rank
  `2r` on one invariant packet type with `r>log_2 m`.  By
  `projective-holonomy-rank-forces-exponential-multiplicity`, commuting return
  letters then force `2^r|m`, an immediate same-model contradiction.  This
  formulation uses only a fixed packet factor plus an adaptive number of
  cocycle directions.
