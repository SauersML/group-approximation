---
rg: 2
id: titz-witzel-sofic-gate-has-only-seven-relators
kind: claim
title: The smallest Titz--Witzel soficity gate has three variables and only seven essential relators
distinct_from:
  titz-witzel-soficity-is-one-finite-csp: That obtains a three-permutation gate with twelve displayed constraints; this proves that five of those constraints are redundant and gives an exact three-variable seven-relator gate.
  titz-witzel-sparse-defect-needs-dense-generator-surgery: That obstructs one construction of approximate solutions to the gate; this is an algebraic Tietze reduction of the gate itself.
artifacts:
  - research/artifacts/titz-witzel-seven-relator-free-word-check.py
---

**THEOREM.**  Use the words `A,B,C,D,E,F,S,H` from `(TWS3)` in
`titz-witzel-soficity-is-one-finite-csp`.  In its presentation `(TWS4)`, the
five square relators

```text
A^2, B^2, F^2, S^2, H^2
```

are consequences of

```text
C^2, E^2, A C D B, x z C S, A E D F, D F E H, D S F E.    (TW7)
```

Consequently the smallest Titz--Witzel group has a presentation on three
generators with seven relators.  An especially symmetric set of variables is
`(c,e,r)=(C,E,z)`.  Put

```text
Y=r^2 e^(-1),                 X=Y^(-2)c,
A'=X Y^(-2),                  B'=r Y^(-1) r,
D'=r Y^(-1) r X Y^(-1),      F'=X^(-1) r^2 Y^(-1) X,
S'=r^(-1) X^(-1) Y r^(-2),   H'=r^2 Y^(-1).                (TW8)
```

Then the group is

```text
<c,e,r | c^2, e^2,
         A' c D' B', X r c S', A' e D' F',
         D' F' e H', D' S' F' e>.                         (TW9)
```

The last three quartics in `(TW9)` have the cleaner equivalent triangular
form

```text
D'=e (A')^(-1) F',       H'=e A' e,       S'=F' A' F'.   (TW9')
```

Thus one may use `c^2,e^2`, the first two quartics in `(TW9)`, and the three
equations `(TW9')` as the seven defining relators.

The marked word is `Y^8`.  Hence soficity of the simple index-two kernel is
equivalent to the existence of triples `(c_n,e_n,r_n)` of finite permutations
for which the seven words in `(TW9)` have normalized Hamming defect tending
to zero and

```text
limsup_n d_H(Y_n^8,1)>0.                                  (TW10)
```

This reduces the terminal feasibility problem from twelve equations to seven,
with only the two bare involution constraints `c^2` and `e^2`.  It does not by
itself supply the required approximate permutation solutions.

**Approximation corollary.**  The two involution constraints can be made exact
without changing the gate.  Equivalently, one may require
`c_n^2=e_n^2=1` for every `n`, ask
only that the five nonsquare words in `(TW9)` (equivalently, its first two
quartics together with `(TW9')`) have defect tending to zero, and
retain the same positive separation objective `(TW10)`.  Thus the genuinely
approximate part of the terminal CSP consists of five equations coupling two
exact matchings and one arbitrary permutation.

---

### Proof

titz-witzel-seven-relator-gate-proof
