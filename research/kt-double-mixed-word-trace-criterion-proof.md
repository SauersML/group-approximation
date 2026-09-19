---
rg: 2
id: kt-double-mixed-word-trace-criterion-proof
kind: route
title: Pass between canonical microstates and the amalgam normal form
target: kt-double-hyperlinear-iff-mixed-word-trace-selection
requires: []
---

Assume first that `D` is hyperlinear and take canonical normalized-Hilbert--
Schmidt microstates `Phi_n:D->U(d_n)`.  Set

```text
rho_(epsilon,n)=Phi_n o i_epsilon.
```

Asymptotic multiplicativity of `Phi_n` gives `(KMW1)`.  Since
`i_0(gamma)=i_1(gamma)` in `D`, `(KMW2)` holds (indeed the two displayed
values are equal for this choice).  Restriction of the canonical character
gives `(KMW3)`.  A reduced alternating word of length at least two is
nonidentity by the amalgam normal-form theorem, so asymptotic
multiplicativity and the canonical trace of `Phi_n` give `(KMW4)`.

Conversely suppose `(KMW1)--(KMW4)`.  Choose once and for all transversals
for the `Gamma` cosets in each copy of `G`, hence a reduced normal form for
every element of `D`.  Define `Phi_n(x)` to be the corresponding product of
the `rho_(epsilon,n)` values of its syllables.

For fixed `x,y in D`, reducing the concatenation of the chosen normal forms
of `x` and `y` to the chosen normal form of `xy` uses only finitely many
vertex multiplications and finitely many moves of elements of `Gamma` from
one vertex copy to the other.  Every vertex multiplication costs `o(1)` by
`(KMW1)`, every change of copy costs `o(1)` by `(KMW2)`, and multiplication
by unitaries preserves normalized Hilbert--Schmidt norm.  The number of
steps depends on `x,y` but not on `n`; the triangle inequality therefore
gives

```text
||Phi_n(xy)-Phi_n(x)Phi_n(y)||_2 -> 0.                  (KMW5)
```

If `x!=1` has normal-form length one, `(KMW3)` gives
`tr(Phi_n(x))->0`.  If it has length at least two, `(KMW4)` gives the same
conclusion.  Thus the induced character is `delta_1`.  Equations `(KMW5)`
and the canonical character are precisely canonical hyperlinear
microstates for `D`, proving the converse.
