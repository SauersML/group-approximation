---
rg: 2
id: sp4-quasirep-windings-are-sublinear
kind: claim
title: Normalized Maslov windings of Sp4(Z) quasi-representations are little-o of the defect
distinct_from:
  sp4-quasirep-windings-budget-and-saturation: that proves the linear upper budget and that the all-MF branch saturates it; this asks for the strictly stronger sublinear bound, which would exclude the all-MF branch.
  deligne-sep8-first-order-tensor-threshold: that phrases the all-MF branch through o(|t|) projective models with a moving parameter; this is a statement about plain quasi-representations of Sp_4(Z) and their integer windings only.
  dadarlat-linear-groups-have-nonzero-h2-windings: that gives nonzero windings at some defect; this asks how small the normalized winding is relative to the defect.
---

**OPEN.** Notation as in `sp4-quasirep-windings-budget-and-saturation`. The claim is that for some relator `r` with
`k != 0` and some finite window `W` containing `W_r`,

```text
S_W(eps) = o(eps)   as eps -> 0.
```

Equivalently, `eps`-quasi-representations of `Sp_4(Z)` on `W` with nonzero winding have
`|kappa_r|/d = o(eps)`. For example, this holds if their dimensions satisfy `eps D_W(eps) -> infinity` uniformly
with bounded windings.

**Why it matters.**
- By item 4 of `sp4-quasirep-windings-budget-and-saturation`, it gives `P_op = (1/m)Z/Z` for one even `m`. It also
  gives the explicit floor `liminf f_W(t)/|t| >= 4|k|/(6g-1)` for the fixed-window projective defect.
- With `3 not | m`, this is the flagship `deligne-triple-cover-exact-mf-radical`. So the flagship is implied by two
  prerequisites, each of which can fail on its own:
  - this claim (a statement about `Sp_4(Z)` alone, with no cover and no parameter);
  - the arithmetic statement `3 not | m`.

**How it can fail.**
- Any saturating sequence: `eps_n`-quasi-representations with `|kappa_r|/d_n >= c eps_n`. For instance, a
  `t`-model with error below `4|k||t|/(6g-1)` for small `t` is one.
- A Dadarlat-type construction with dimension `d_n = O(1/eps_n)`.
- Item 3 of the budget node shows it must fail if `P_op = R/Z`. So refuting it is necessary, though not known to be
  sufficient, for the all-MF branch.

## Attempts
- **2026-09-18, swarm-0917-w7-w7-deligne-break: posed.** The Dadarlat construction goes through quasidiagonality and
  gives no dimension control, so it decides neither side. No test has been run.
- **2026-09-18, swarm-0917-w7-w7-deligne-follow (cohomology-index): the determinant class is killed, and the
  prerequisite is weakened.** See `sp4-winding-ratio-sharp-constant-is-gromov-dual`, ESTABLISHED.
  - *Exact formula.* `kappa_r/d = <beta_pi, c_r>`, where `beta_pi = (1/(2 pi i d)) Tr log D` is the determinant
    cocycle of the defects and `c_r` is the relator 2-cycle.
  - *Sharp constants.* The ratio `limsup S_W/eps` is at most `N_W/(2 pi)`, and `N_W` decreases to `nu`, the l1
    seminorm of `[r]`. `P_op = R/Z` forces the ratio to at least
    `|k|/(2 pi beta*_W)` on every window, a bound that increases to the same `nu/(2 pi)`.
  - *Class kill.* Item 8: the determinant relaxation, meaning local cocycle, the `a(eps)` bound and integrality, is
    solved by `lambda (b + delta psi*)` with ratio `|k|/(2 pi beta*_W)`. So Tr log, determinant, `K_1` and
    winding-integrality arguments cannot prove this claim, nor even the weaker deficit. Such an argument dies at the
    bound on `<beta_pi, c_r>`. Any proof must control the traceless part of the defects.
  - *Weaker route.* The flagship needs only `sp4-quasirep-winding-ratio-has-a-deficit`, a strict inequality against
    the explicit constant, via `deligne-triple-cover-via-winding-deficit`. This claim implies that one
    (`sp4-quasirep-winding-ratio-has-a-deficit-from-sublinear`).
