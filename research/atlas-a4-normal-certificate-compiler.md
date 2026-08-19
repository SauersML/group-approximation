---
rg: 2
id: atlas-a4-normal-certificate-compiler
kind: claim
title: Five conjugacy loops, one collision readout and six local opcode semantics suffice for the A8 chart frame
distinct_from:
  atlas-a4-full-packet-normal-generator-table-compiler: that stronger target constructs a 20160-state approximate multiplication table; this target keeps only five nontrivial conjugacy identities for six standard chart transvections.
  atlas-a4-full-packet-normal-generator-holonomy-compiler: that stronger target rounds residual holonomy to an exact A8 representation; this target neither rounds nor constructs an approximate representation.
artifacts:
  - experiments/atlas_a8_transvection_normal_certificates.py
  - experiments/atlas_a4_19243_normal_closure.py
---

Use the six adjacent standard chart transvections

```text
S={t01,t10,t12,t21,t23,t32} subset GL_4(F2)=A8.
```

By `atlas-a8-six-transvection-normal-certificates`, these six elements generate
all of `A8`, the collision translation is exactly `b=t23`, and for every
`s in S` there is a frozen shortest word `a_s` in `S` with

```text
s=a_s b a_s^-1.                                         (A4-NCERT-0)
```

For `s=t23` this is tautological, so there are only **five nontrivial
certificate relations**

```text
r_s=s^-1 a_s t23 a_s^-1=1,      s != t23.
```

For every normalized exact-regular A4 context network `sigma_n,U_n,eta_n`
from the holonomy route, construct unitary opcodes `V_n(s)` for the six
transvections and constants `C_cert,C_col,C_sem<infinity`, independent of `n`,
such that

```text
max_(s in S\{t23}) ||r_s(V_n)-1||_2
 <= C_cert eta_n,                                       (A4-NCERT-1)

||V_n(t23)-1||_2
 <= C_col (||sigma_n(q_19243)-1||_2 + eta_n),           (A4-NCERT-2)

max_(s in S)
 ||V_n(s)-U_n lambda_(k_n)(s) U_n^* lambda_(k_n)(s)^*||_2
 <= C_sem eta_n.                                        (A4-NCERT-3)
```

The third line is only **local opcode semantics**: `V_n(s)` must read the six
chart-to-chart covariance commutators.  It is no longer a global decoder
hypothesis.  The established `atlas-a8-six-transvection-commutant-gap` turns
these six local semantics into distance from the full regular `A8` commutant
after the opcodes collapse.

Thus the compiler never labels the 20160 group states, never checks arbitrary
products `xy=z`, never rounds a representation, and never proves a separate
global decoder estimate.  Its complete interface is five bounded conjugacy
loops, one collision readout, and six bounded semantic readouts.

The central-`C3` packet directions remain essential **inside the proof of the
five conjugacy loops**: the fourteen-word affine core alone cannot transport
`t23` through the whole chart.  They no longer need to survive as separate
output opcodes or table states.

## Attempts

- **Compile the five frozen loops directly.**  Substitute the explicit
  conjugator words of `atlas-a8-six-transvection-normal-certificates` into the
  four-rectangle tree gauge.  Each `r_s` is a fixed bounded closed walk; prove
  its evaluated defect is `O(eta_n)` by finite telescoping.
- **Exploit single-collision multiplicity.**  Every nontrivial certificate uses
  exactly one occurrence of `t23`, so `atlas-a8-five-conjugacy-hs-collapse`
  propagates the collision with constant one and no normal-closure diameter.
- **Derive opcode semantics before any group law.**  The six matrices in
  `(A4-NCERT-3)` are concrete commutator residuals of the relative chart frame.
  Try to read them directly on the canonical qutrit multiplicity wires after
  the two biclique tree gauges; no A8 multiplication consistency is needed.
- **Search packet-local rewrites, not shorter A8 words.**  The exact BFS already
  minimizes conjugator length.  Optimize instead the number of distinct
  rectangle/stable-letter residuals touched by the five frozen loops and the
  six semantic readouts.
