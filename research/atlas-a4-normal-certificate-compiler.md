---
rg: 2
id: atlas-a4-normal-certificate-compiler
kind: claim
title: Five fixed conjugacy checks and the 19243 readout suffice to kill the A8 chart frame
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
all of `A8`, the collision translation is exactly

```text
b=t23,
```

and for every `s in S` there is a frozen shortest word `a_s` in `S` with

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
transvections and constants `C_cert,C_col,C_dec<infinity`, independent of `n`,
such that

```text
max_(s in S\{t23}) ||r_s(V_n)-1||_2
 <= C_cert eta_n,                                       (A4-NCERT-1)

||V_n(t23)-1||_2
 <= C_col (||sigma_n(q_19243)-1||_2 + eta_n),           (A4-NCERT-2)

dist_2(U_n,lambda_(k_n)(A8)')
 <= C_dec (max_(s in S)||V_n(s)-1||_2 + eta_n).         (A4-NCERT-3)
```

This is strictly less structure than an approximate A8 multiplication table.
The compiler never labels the 20160 group states, never checks arbitrary
products `xy=z`, and never reconstructs an approximate representation.  It
only has to certify five bounded conjugacy loops, read the one collision
transvection, and expose the six-generator commutant decoder.

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
  exactly one occurrence of `t23`, so the abstract normal-certificate theorem
  has `M=1`.  There is no accumulation through a normal-closure diameter.
- **Search for packet-local rewrites, not shorter A8 words.**  The exact BFS
  already minimizes the conjugator length in the six-transvection alphabet.
  The useful optimization is instead to rewrite each frozen loop into the
  smallest set of packet rectangle/stable-letter residuals.
- **Decoder last.**  The six transvections generate `A8`, so their commutant is
  exactly the full regular-chart commutant.  Once the six opcodes collapse,
  `(A4-NCERT-3)` should be a fixed finite Poincare estimate rather than a
  20160-state reconstruction problem.
