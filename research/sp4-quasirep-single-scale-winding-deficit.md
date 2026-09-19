---
rg: 2
id: sp4-quasirep-single-scale-winding-deficit
kind: claim
title: At one fixed defect scale and on one finite window, no Sp4(Z) quasi-representation reaches the all-MF winding ratio
distinct_from:
  sp4-quasirep-winding-ratio-has-a-deficit: that is a limsup inequality as the defect tends to zero; this is one inequality at one fixed defect scale, which may be as large as 1/(6g-1). They are equivalent by sp4-winding-ratio-is-an-infimum-over-scales, but this form fixes the quantifier on the scale.
  sp4-quasirep-windings-are-sublinear: that asks for the ratio to tend to zero; this asks for one scale where it falls below one explicit positive constant.
  sp4-winding-ratio-is-an-infimum-over-scales: that is the unconditional superadditivity theorem; this is the open inequality it reduces the deficit hole to.
---

**OPEN.** Notation as in `sp4-winding-ratio-is-an-infimum-over-scales`, with `a_g = 1/(6g-1)` and
`tau_W = |k|/(2 pi beta*_W)`. The claim is that for some relator `r` with `k != 0`, some finite window `W`
containing `W_r`, and some single scale `eps_1 in (0, a_g]`, there is `c < tau_W` with

```text
|kappa_r(pi)| <= c eps_1 d     for every d >= 1 and every unital pi : Gamma -> U(d)
                               with defect <= eps_1 on W.                           (SSD)
```

A sufficient window-free form: some `(W, eps_1)` with `S_W(eps_1) < eps_1 nu/(2 pi)`.

**Why it matters.**
- By item 4 of `sp4-winding-ratio-is-an-infimum-over-scales`, (SSD) is equivalent to
  `sp4-quasirep-winding-ratio-has-a-deficit` (route `sp4-winding-deficit-from-one-scale`).
- So, with `deligne-finite-parameter-group-has-period-prime-to-three`, it gives the flagship
  `deligne-triple-cover-exact-mf-radical` via `deligne-triple-cover-via-winding-deficit`.
- It is a statement about one defect scale, uniform in the dimension. Fixed-defect rigidity (for instance a
  quantitative spectral-gap or Kazhdan-pair argument whose constants are allowed to depend on `eps_1`) is the kind of
  tool that can prove it, whereas the limsup form asks for control as `eps -> 0`.

**How it can fail.** It fails exactly when saturation holds at every scale: for every admissible relator `r`, every
`W` and every `eps in (0, a_g]`, `S_W(eps) >= tau_W eps`. By item 5 of the theorem node this is forced if `P_op = R/Z`.

**What cannot prove it.**
- Scalar data. By item 7 of the theorem node, the determinant relaxation exceeds `tau_W eps` at every scale, so
  Tr-log, determinant, `K_1` and winding-integrality arguments fail at each fixed scale too. A proof must use the
  traceless part of the defects.
- Finite computation alone. (SSD) quantifies over all dimensions `d`; a census in bounded dimension gives only
  lower bounds on `S_W(eps_1)`, which cannot prove it.

## Attempts
- **2026-09-18, swarm-0917-w14-w14-deligne-last1: posed.** Obtained from the deficit hole by the superadditivity
  theorem. No fixed-scale argument has been tried.
