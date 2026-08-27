---
rg: 2
id: central-clifford-parity-sector-rounding-proof
kind: route
title: Put each commutation-sign row in the code and discard only the nonabelian central sectors
target: central-clifford-parity-sectors-round-uniformly
requires: []
---

Fix a central summand and suppress `omega`.  The sign matrix `B=(b(i,j))`
is alternating.  For a parity row `h_a`, exact parity and centrality of all
commutators give, for every `j`,

```text
1=[prod_(i:h_a(i)=1) Q_i,Q_j]
 =(-1)^(sum_i h_a(i)b(i,j)).                              (CCP4)
```

Thus every column, and hence every row, of `B` lies in `ker(H)=C`.  If `B`
is nonzero, one of its rows has weight at least `delta L`.  Alternation
makes each index in that row index another nonzero row, each again of weight
at least `delta L`.  Therefore

```text
|{(i,j):b(i,j)=1}| >= delta^2 L^2.                        (CCP5)
```

On this summand a negative commutation sign contributes exactly `4` to the
squared normalized Hilbert--Schmidt commutator norm.  If `p_bad` is the sum
of the central summands with nonzero `B`, equations `(CCP2)` and `(CCP5)`
therefore imply

```text
tau(p_bad) <= E_com/(4 delta^2).                          (CCP6)
```

On `1-p_bad` all the `Q_i` commute and retain the exact parity relations.
Define

```text
Q_i'=(1-p_bad)Q_i+p_bad I.                               (CCP7)
```

These are commuting reflections satisfying every homogeneous parity check.
Moreover

```text
||Q_i-Q_i'||_2^2=||p_bad(Q_i-I)||_2^2 <=4 tau(p_bad).
```

Average over `i` and use `(CCP6)` to obtain `(CCP3)`.  The joint spectral
PVM of the `Q_i'` is automatically supported on `C`, so the correction is
the required same-Hilbert code PVM in this central-Clifford model class.

