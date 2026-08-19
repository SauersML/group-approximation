---
rg: 2
id: atlas-a4-normal-certificate-compiler
kind: claim
title: The full A4 packet compiles only the finite normal-generation certificates needed to kill the chart frame
distinct_from:
  atlas-a4-full-packet-normal-generator-table-compiler: that stronger target constructs a 20160-state approximate multiplication table; this target keeps only finitely many normal-generation identities for a fixed packet-opcode generating set.
  atlas-a4-full-packet-normal-generator-holonomy-compiler: that stronger target rounds residual holonomy to an exact A8 representation; this target neither rounds nor constructs an approximate representation.
artifacts:
  - experiments/atlas_a4_19243_normal_closure.py
  - experiments/atlas_a4_19243_parabolic_ladder.py
---

Fix once and for all a finite packet-opcode generating set

```text
S subset A8 ~= GL_4(F2)
```

which contains the collision translation `b`, generators for the two visible
rank-three/S3 packet directions, and one nontrivial central-`C3` escape opcode.
By `atlas-a4-19243-parabolic-normal-closure`, `<<b>>_A8=A8`.  Therefore for
each `s in S` choose once and for all a finite normal-generation identity

```text
s = prod_j a_(s,j) b^(eps_(s,j)) a_(s,j)^-1            (A4-NCERT-0)
```

inside `A8`, and let `r_s` be the corresponding relation word.

For every normalized exact-regular A4 context network `sigma_n,U_n,eta_n`
from the holonomy route, construct one unitary opcode `V_n(s)` for each
`s in S` and constants `C_cert,C_col,C_dec<infinity`, independent of `n`, so
that

```text
max_(s in S) ||r_s(V_n)-1||_2
 <= C_cert eta_n,                                       (A4-NCERT-1)

||V_n(b)-1||_2
 <= C_col (||sigma_n(q_19243)-1||_2 + eta_n),           (A4-NCERT-2)

dist_2(U_n,lambda_(k_n)(A8)')
 <= C_dec (max_(s in S)||V_n(s)-1||_2 + eta_n).         (A4-NCERT-3)
```

This is strictly less structure than an approximate A8 multiplication table.
The compiler never labels all 20160 group states and never checks arbitrary
products `xy=z`; it checks only the fixed normal-generation certificate words
whose sole job is to propagate the one collision readout `b≈1` to the finite
opcode set seen by the decoder.

## Attempts

- **Normal-closure circuit rather than Cayley table.**  Run a shortest-path
  search in the normal-closure graph of `b` and minimize the total packet-edge
  support of the identities `(A4-NCERT-0)`.  The optimization objective is the
  number of distinct bounded context loops that must be controlled, not word
  length by itself.
- **Exploit that the collision is already a transvection.**  In the audited
  `GL_4(F2)` coordinates, the repeated first-chart syllable of `q_19243` is a
  standard transvection.  The standard chart generators are transvections as
  well, so conjugacy should make most certificates one-conjugate identities;
  only the central-`C3` escape/gluing opcodes should need longer words.
- **Compile relation words directly through the tree gauge.**  Each fixed
  `r_s` is a bounded closed walk in the four-rectangle packet groupoid.  Prove
  its evaluated defect is `O(eta_n)` by finite telescoping.  No consistency
  statement for products not appearing in the certificate is required.
- **Decoder last.**  Once the opcode tuple collapses, `(A4-NCERT-3)` is only a
  finite commutant/Poincare estimate for the exact regular chart; do not
  reconstruct unused A8 states merely to obtain it.
