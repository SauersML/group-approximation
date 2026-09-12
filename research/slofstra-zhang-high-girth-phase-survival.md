---
rg: 2
id: slofstra-zhang-high-girth-phase-survival
kind: claim
title: High-girth solution-group incidence protects the central phase by planar curvature
artifacts:
  - research/artifacts/slofstra-papers-focused-audit-2026-08-20.md
distinct_from:
  congruence-transporter-girth: that is a metric lower bound in finite congruence quotients; this is an exact van Kampen-picture obstruction inside one solution group.
  non-ce-bcs-has-robust-approximate-energy-gap: that is a finite-dimensional normalized-HS compactness gap; this theorem proves exact nontriviality of a central phase and supplies no approximate-representation modulus.
---

Let `2<=p<=infinity`, let `A` be an integer matrix whose nonzero entries are
non-zero-divisors in `Z_p` (equivalently, are coprime to finite `p`), and let
`H(A)` be its incidence hypergraph.  If

```text
(minimum vertex degree, girth) is at least (4,4) or (3,6),
```

then the distinguished central generator `J` has exact order `p` in the
solution group `Gamma_p(A,b)` for every right-hand side `b`.

The mechanism is diagrammatic.  A nonzero power `J^k=1` would give a closed
picture of phase `k`.  Minimal-picture reductions force vertex degree at
least `d`; incidence girth forces every face to have size at least `g`.
For `(d,g)=(4,4)` or `(3,6)`, Euler curvature rules out such a nonempty planar
picture, while a one-face minimal picture is also empty.  Hence its phase is
zero.

This is Theorem 1.3 and the proof in Section 2 of Slofstra--Zhang,
*Operator solutions of linear systems and small cancellation*,
arXiv:2412.10305v2.  The v2 non-zero-divisor hypothesis is essential.
