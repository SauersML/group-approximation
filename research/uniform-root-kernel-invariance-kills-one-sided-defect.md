---
rg: 2
id: uniform-root-kernel-invariance-kills-one-sided-defect
kind: claim
title: Uniform root-kernel invariance kills the one-sided defect with no Kazhdan input
distinct_from:
  finite-additive-order-one-sided-defects-are-mf-invisible: that is the corona statement for the same defect and consumes property (T) through Ershov--Jaikin-Zapirain; this is a finite-dimensional statement with an explicit uniform constant and no Kazhdan input at all, and by root-kernel-invariance-is-not-pointwise-obtainable it does not imply the corona one.
  finite-root-algebra-forces-steinberg-triviality: that routes the same root-kernel observation through a two-sided ideal and simplicity of the binary Leavitt algebra, and concludes that the whole representation is trivial; this needs invariance under two LEFT multiplications only, assumes no simplicity and no fullness, and concludes only that the defect roots die.
  window-controlled-finite-dimensional-root-theorem: that is the Kervaire--Laudenbach lane's hypothesis about evaluation paths of a group word staying inside a control window; this is a spectral separation statement about additive root maps of a ring, and shares only the word window.
artifacts:
  - research/artifacts/root-kernel-uniformity-gap-2026-09-08.md
---

**ESTABLISHED.**  Let `R` be unital with `mR = 0` for some `m >= 2`, let
`ts = 1` in `R`, put `q = 1 - st`, and set

```text
kappa_m = 2 sin(pi/m).                                                (RK1)
```

Let `X, Y : (R,+) -> U(d)` be **genuine** homomorphisms of additive groups and
let `C, U_s, U_t in U(d)`.  If for **every** `a in R`

```text
|| C X(a) C* - Y(a) ||       <  kappa_m,                              (RK2)
|| [U_b, X(a)] - Y(ba) ||    <  kappa_m       (b = s, t),             (RK3)
```

then

```text
X(qa) = Y(qa) = 1        for every a in R.                            (RK4)
```

**No property (T) is used, and no simplicity or fullness of any ideal.**  The
common kernel `I = ker X = ker Y` is not required to be a two-sided ideal;
invariance under the two left multiplications by `s` and `t` is what the proof
consumes, and it makes `R/I` a finite additive group on which `ts = 1` forces
`st = 1`.

**Consequence for exact representations.**  Let `rho` be any finite-dimensional
unitary representation of `E_n(R)`, `n >= 3`, and take

```text
X(a) = rho(e_23(a)),   Y(a) = rho(e_13(a)),   U_b = rho(e_12(b)),
C = rho(w),            w = e_12(1) e_21(-1) e_12(1).
```

The elementary identities `w e_23(a) w^-1 = e_13(a)` and
`[e_12(b), e_23(a)] = e_13(ba)` make `(RK2)` and `(RK3)` hold with error `0`,
so `rho` kills `e_13(qa)` for every `a`, and conjugating by signed permutation
matrices carries this to every off-diagonal position.  Thus **every exact
finite-dimensional unitary representation of `E_n(R)` kills the defect roots**,
for `n >= 3` and `R` of positive characteristic, with no Kazhdan input.

**It does not give the corona statement.**  `(RK2)`--`(RK3)` are quantified at
one coordinate over all coefficients; a corona representation supplies the
reverse order, and `root-kernel-invariance-is-not-pointwise-obtainable`
exhibits models in which every fixed test is eventually exact while the
hypotheses fail at distance `2` at every coordinate.  The corona theorem is
`finite-additive-order-one-sided-defects-are-mf-invisible`, which still
consumes property (T); this claim does not discharge
`property-t-free-jacobson-head-collapse` or any of its siblings.
