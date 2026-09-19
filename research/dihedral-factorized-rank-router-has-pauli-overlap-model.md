---
rg: 2
id: dihedral-factorized-rank-router-has-pauli-overlap-model
kind: claim
title: The minimal D8 factorized rank router has an exact forbidden Pauli gauge model
artifacts:
  - research/artifacts/hybrid-rank-router-tensor-closure-2026-08-23.md
distinct_from:
  controlled-reflection-cell-has-free-orientation: that records an uncontrolled multiplicity orientation for one Pauli controller; this computes the complete two-lift D8 assembler and shows its rank-conjugacy relation can vanish at full forbidden overlap.
  hybrid-rank-router-tensor-closure-obstruction: that refutes every universal router categorically; this gives the explicit zero-defect matrix escape for the proposed nested-D8 starting cell.
---

**ESTABLISHED COUNTERMODEL.**  Work in the negative spin sector of

```text
D8=<m,z,j | m central, m^2=z^2=j^2=1, zj=mjz>.
```

Let commuting payload involutions `a,b` centralize `D8`.  The minimal
factorized assembler introduces block-diagonal involutions `r,s` with

```text
(rj)^2=a,       (sj)^2=b,
[r,b]=[s,a]=[r,s]=1.                                  (DFR1)
```

After identifying the two role halves by `j`, every exact solution has

```text
r=diag(AW,W),          s=diag(BV,V),                  (DFR2)
```

where `W,V,A,B` are commuting involutions.  Therefore the natural output
words are only gauge-twisted hybrids:

```text
R=rjsj=diag(AG,BG),     S=rs=diag(ABG,G),
G=WV.                                                       (DFR3)
```

The gauge can erase the rank checksum at full forbidden overlap.  On a
two-dimensional multiplicity space take

```text
A=B=-I,       W=Z,       V=I,       U=I_role tensor X,
XZX=-Z.                                                     (DFR4)
```

Then every relation in `(DFR1)` is exact, while

```text
P=Q=I,        R=-I_role tensor Z,
S= I_role tensor Z,       U R U^*=S.                    (DFR5)
```

Thus the stable rank-conjugacy relator has zero defect although
`||PQ||_2^2=1`.  The two-letter D8 swap identity can route one block, but
assembling both hybrid blocks by these factorization cells leaves exactly
the transverse Pauli multiplicity gauge needed to cancel the trace
obstruction.
