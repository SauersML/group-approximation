---
rg: 2
id: titz-witzel-sofic-gate-two-generators-four-approximate-relators
kind: claim
title: The smallest Titz--Witzel soficity gate has two variables and four genuinely approximate relators
distinct_from:
  titz-witzel-sofic-gate-has-only-seven-relators: That gives a three-variable seven-relator presentation with two exact involutions and five other constraints; this eliminates one permutation and one approximate constraint.
  titz-witzel-trivial-second-matching-collapses-mark: That proves the second matching cannot disappear asymptotically; here the surviving exact matching is retained and the other matching is algebraically reconstructed as a word.
artifacts:
  - research/artifacts/titz-witzel-two-generator-free-word-check.py
---

**THEOREM.**  Let `barGamma` be the smallest Titz--Witzel group from
`titz-witzel-soficity-is-one-finite-csp`.  It has a presentation on two
generators `(e,u)` with five relators, only one of which is a bare square.
Define the following words successively in the free group on `(e,u)`:

```text
h   = u e u^(-1),             a   = e h e,
x   = a u^2,                  c   = u^2 a u^2,
f   = x^(-1) h x,             d   = e a^(-1) f,
s   = f a f,                  rho = x^(-1) s^(-1) c^(-1),
b   = rho u^(-1) rho.                                      (TW2G1)
```

Then

```text
barGamma = <e,u |
  e^2,
  c^2,
  rho^2 e^(-1) u^(-1),
  b x u^(-1) d^(-1),
  a c d b>.                                                (TW2G2)
```

Under the exact Tietze equivalence with `(TW9)`, one has

```text
u=Y,       rho=r,       c=C,       e=E.                    (TW2G3)
```

In particular the separating word is literally `u^8`.

Consequently soficity of the simple index-two kernel is equivalent to the
existence of pairs `(e_n,u_n)` of finite permutations such that

```text
e_n^2=1
```

at every stage, the last four relators in `(TW2G2)` have normalized Hamming
defect tending to zero, and

```text
limsup_n d_H(u_n^8,1)>0.                                  (TW2G4)
```

Thus the terminal finite problem has two permutation variables, one exact
matching, and four genuinely approximate equations.  This is an exact
algebraic and quantitative reduction of the previous gate; it does not by
itself construct the required pairs.

---

### Proof

titz-witzel-two-generator-gate-proof
