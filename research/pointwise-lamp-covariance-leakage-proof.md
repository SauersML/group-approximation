---
rg: 2
id: pointwise-lamp-covariance-leakage-proof
kind: route
title: Move a finite character frontier while every fixed lamp has already stabilized
target: pointwise-lamp-covariance-has-half-mass-leak
requires: []
---

Write lamps as finite subsets of `A`, with addition given by symmetric
difference.  Since left multiplication by `s != 1` moves every point, one can
choose an increasing finite exhaustion `(E_n)` of `A` with

```text
s E_n != E_n                                                        (1)
```

for every `n`.  Inductively, after adjoining the next point of a fixed
enumeration, choose `x` outside the resulting finite set together with its
`s`-translate and adjoin `x`.  Then `s x` witnesses `(1)`.

For a finite subset `E` define the character

```text
chi_E(m)=(-1)^(|supp(m) intersect E|).
```

Put

```text
rho_n(m)=diag(1,chi_(E_n)(m)).                                  (2)
```

This is an exact representation of the whole elementary abelian group `M`.
Its joint character PVM has the rank-one atoms `P_1` and `P_(chi_(E_n))`.

For every fixed `m`, exhaustion gives

```text
chi_(E_n)(m)=(-1)^(|supp(m)|)=chi_all(m)                         (3)
```

for all large `n`, where `chi_all` is the invariant total-parity character.
The same holds for every fixed translate `g.m`.  Since translation preserves
support cardinality, `(3)` gives

```text
rho_n(g.m)=rho_n(m)
```

eventually.  Taking every actor lift to be `I_2` proves `(PCL1)`.  More
explicitly, for fixed `(m,g),(m',h) in Gamma`,

```text
sigma_n((m,g)(m',h)) = rho_n(m+g.m')
                      = rho_n(m+m')
                      = sigma_n(m,g)sigma_n(m',h)
```

for all sufficiently large `n`.  Thus `(sigma_n)` induces the corona
homomorphism whose lamp restriction is `diag(1,chi_all)` and whose actor
restriction is trivial.

Now compute the fine transport leakage, extending the two-atom PVM by zero
on every absent character.  Under the dual action,

```text
s.chi_(E_n)=chi_(s E_n).
```

Characters of the full regular lamp module are literally subsets of `A`, so
`(1)` says `chi_(s E_n) != chi_(E_n)`.  It is also different from the trivial
character.  Since `U_(s,n)=I_2`, the trivial atom is transported correctly,
whereas the entire moving rank-one atom misses its prescribed target:

```text
L_s = tr((1-P_(s.chi_(E_n))) P_(chi_(E_n)))
    = tr(P_(chi_(E_n)))
    = 1/2.
```

This is `(PCL2)`.  Amplification repeats both atoms with the same
multiplicity, and a direct sum forms the normalized weighted average of the
coordinate leakages, so both operations preserve `1/2`; subsequences plainly
do as well.

Finally, replacing `chi_(E_n)` by `chi_all` gives an exact covariant
zero-leakage lift of the same corona class.  But for each `n` choose
`x in E_n symmetric_difference A`, equivalently `x notin E_n`; on the
single lamp `m_x`, the two characters have opposite signs, so the two lifts
are operator-norm distance `2`.  As `x` necessarily moves with `n`, this does
not contradict their eventual equality on every fixed lamp.  It proves that
choosing the good lift requires uniform whole-module information absent from
pointwise corona covariance.

For the final calibration take `A=F_2`.  A nontrivial left translation
stabilizing a finite nonempty set would act on it as a finite permutation,
so some positive power would fix a point; torsion-freeness of `F_2` rules
this out.  Hence the orbit of each `chi_(E_n)` is the regular `F_2` orbit.
Kesten's calculation for the four-generator simple random walk gives norm
`sqrt(3)/2` and gap `1-sqrt(3)/2`.

In the complete energy, the block from `chi_(E_n)` to its absent target has
normalized squared mass `1/2`.  The absent atom at
`s^(-1).chi_(E_n)` has prescribed target `chi_(E_n)`, contributing the other
`1/2`; hence `E_(s,n)=1`.  Finally

```text
rho_n(delta_e)=diag(1,-1),
z=[[0,1],[1,0]],
[rho_n(delta_e),z]=-I=J,
```

so the mark is fully separated with zero seed defect.
