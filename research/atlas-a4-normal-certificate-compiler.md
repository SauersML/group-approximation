---
rg: 2
id: atlas-a4-normal-certificate-compiler
kind: claim
title: Five opaque conjugacy transports and the 19243 readout suffice for the A8 chart frame
distinct_from:
  atlas-a4-full-packet-normal-generator-table-compiler: that stronger target constructs a 20160-state approximate multiplication table; this target asks only for five pairwise conjugacy transports around the collision opcode.
  atlas-a4-full-packet-normal-generator-holonomy-compiler: that stronger target rounds residual holonomy to an exact A8 representation; this target never constructs even an approximate representation.
artifacts:
  - experiments/atlas_a8_transvection_normal_certificates.py
  - experiments/atlas_a4_19243_normal_closure.py
---

Use the six adjacent standard chart transvections

```text
S={t01,t10,t12,t21,t23,t32} subset GL_4(F2)=A8,
```

with collision translation `b=t23`.  For a normalized exact-regular A4 context
network `sigma_n,U_n,eta_n`, do **not** construct abstract opcode semantics.
Define the six opcodes directly from the relative chart frame:

```text
V_n(s)=U_n lambda_(k_n)(s) U_n^* lambda_(k_n)(s)^*.    (A4-STAR-0)
```

Thus `||V_n(s)-1||_2` is exactly the chart-to-chart covariance defect of `s`.
Construct only five auxiliary unitaries

```text
A_n(s),       s in S\{t23},
```

and constants `C_star,C_col<infinity`, independent of `n`, such that

```text
max_(s in S\{t23})
 ||V_n(s)-A_n(s)V_n(t23)A_n(s)^*||_2
 <= C_star eta_n,                                       (A4-STAR-1)

||V_n(t23)-1||_2
 <= C_col (||sigma_n(q_19243)-1||_2 + eta_n).           (A4-STAR-2)
```

That is the whole compiler interface.  The transports `A_n(s)` are deliberately
**opaque**: they need not represent the frozen A8 conjugator words, satisfy any
multiplication law, agree with one another, or even be close to a canonical
matrix.  `unitary-star-conjugacy-hs-collapse` uses only that conjugation is an
HS isometry.  Once `(A4-STAR-1)` and `(A4-STAR-2)` hold, all six raw covariance
commutators collapse, and `atlas-a8-six-transvection-commutant-gap` supplies the
global regular-chart decoder automatically.

The exact A8 audit remains important only as finite design evidence: every one
of the six standard transvections is genuinely conjugate to `t23`, so a
five-edge star is the correct finite incidence pattern.  But the analytic
compiler no longer has to preserve the conjugating **words**.  This removes the
last unnecessary group-law layer from the portfolio.

## Attempts

- **Extract transports, not relations.**  In the canonical qutrit/multiplicity
  splitting of each exact A4 context, identify a packet path carrying the
  `t23` covariance block to each of the other five standard covariance blocks.
  The resulting multiplicity transport itself may be `A_n(s)`; only its two
  endpoints matter.
- **Tree-gauge the packet first.**  After the `K_(2,2) disjoint_union K_(2,4)`
  gauge there are only four rectangle holonomies.  Search for five bounded
  paths in this four-holonomy network whose endpoint conjugacy errors telescope
  to `O(eta_n)`.  There is no need to close those paths into A8 word identities.
- **Use central C3 edges only where the star leaves the affine parabolic.**  The
  fourteen-word rank-three core cannot conjugate `t23` through the whole chart.
  The discarded central-`C3` packet directions should occur exactly in the star
  transports whose endpoints leave that core.
- **Collision readout separately.**  Track the eight syllables of `q_19243`
  through the same tree gauge only far enough to prove `(A4-STAR-2)`.  Do not
  make the five transport proofs depend on a reconstructed collision word.
- **Finite search objective.**  Minimize, for each star edge, the number of
  distinct packet rectangle/stable-letter residuals used by a transport.  Word
  length in A8 is no longer the relevant complexity measure.
