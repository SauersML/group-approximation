---
rg: 2
id: titz-witzel-two-generator-gate-proof
kind: route
title: Eliminate the first matching and then the arbitrary permutation from the seven-relator Titz gate
target: titz-witzel-sofic-gate-two-generators-four-approximate-relators
requires:
  - titz-witzel-sofic-gate-has-only-seven-relators
---

Start with the variables and words `(c,e,r)` and
`Y,X,A,B,D,F,S,H` in `(TW8)--(TW9')`.  Introduce a generator `u` with

```text
u=Y=r^2e^(-1).                                             (1)
```

The relator `e^2=1` and the definitions in `(TW8)` give

```text
H=r^2u^(-1)=u e u^(-1)=h.                                 (2)
```

The middle triangular relation `H=eAe` therefore solves for `A`:

```text
A=eHe=e h e=a.                                             (3)
```

Since `A=Xu^(-2)` and `X=u^(-2)c`, equations (3) solve the old matching and
the word `X` without adding a relation:

```text
c=u^2 a u^2,                 X=a u^2.                      (4)
```

The definitions of `F` and the other two triangular equations now give

```text
F=X^(-1)HX=f,              D=eA^(-1)F=d,
S=FAF=s.                                                     (5)
```

The second of the two remaining quartics in `(TW9)` is `X r c S=1`.
It solves the last old generator:

```text
r=X^(-1)S^(-1)c^(-1)=rho.                                  (6)
```

Finally `B=r u^(-1)r=b`.  After these successive eliminations, exactly four
old conditions remain.  The old square `c^2` is the first.  Equation (1),
the defining equality `D=B X u^(-1)`, and the first remaining quartic
`A c D B=1` become, respectively,

```text
rho^2 e^(-1) u^(-1)=1,
b x u^(-1) d^(-1)=1,
a c d b=1.                                                  (7)
```

Together with `e^2=1`, these are precisely `(TW2G2)`.

For completeness, the reverse construction uses no hidden quotient.  Given
`e,u` satisfying `(TW2G2)`, define all words in `(TW2G1)`, and put
`r=rho`.  The third relator of `(TW2G2)` gives `u=r^2e^(-1)`.  Equations
(2)--(5) then identify the derived words with the words in `(TW8)` and make
all three triangular relations hold.  Definition (6) makes
`X r c S=1`; the fourth relator gives `D=B X u^(-1)`; and the fifth gives
`A c D B=1`.  The first two relators are exactly the two square constraints
`e^2=c^2=1`.  Hence all seven relators of `(TW9)` hold.  The forward and
reverse substitutions fix `e,u` and recover `c,r`, so they are inverse
Tietze maps.  The old marked word `Y^8` is literally `u^8`.

It remains to justify the sharpened approximation statement.  Finite
sequences of Tietze substitutions are quantitative in every bi-invariant
metric: evaluation of a fixed word is Lipschitz in each letter, and an
equation that solves a generator makes that generator close to its solving
word by exactly the equation's defect.  Applying the substitutions
(1)--(6) therefore transports vanishing defects in both directions while
leaving the marked word unchanged.

In the reverse direction the reconstructed word `c(e,u)` need only satisfy
`d_H(c(e,u)^2,1)=o(1)`.  Round this approximate involution cycle by cycle to
an exact involution `c_0`, with

```text
d_H(c,c_0) <= d_H(c^2,1).
```

Replacing `c` by `c_0` perturbs every fixed old relator by `o(1)` and does
not change `u^8`.  Thus the old gate may again be taken with both matchings
exact.  Conversely the exact old matchings certainly give an exact `e` and
the four displayed defects tend to zero after the Tietze substitutions.
This proves the equivalence in `(TW2G4)`.
