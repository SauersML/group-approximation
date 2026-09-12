---
rg: 2
id: intermediate-native-arm-orbit-cut-fence-proof
kind: route
title: Diagonalize one Singer orbit and realize the two-arm menu with an independent finite gauge
target: intermediate-native-arm-orbit-cuts-retain-the-return-gauge
requires:
  - reverse-return-has-native-arm-leavitt-diamond
  - native-inverse-pair-seven-orbits-retain-external-gauge
  - fixed-packet-correction-retains-multiplicity-gauge
---

Work first on the `n=-1` sector.  The exact table `(NIO7)` is the
symplectic pairing table of one Singer orbit in `F_2^3` with one dual
Singer orbit.  Its row rank is three.  Hence, after a finite unitary change
of coordinates,

```text
p_k=X_(M^k a),            q_l=Z_(M^(-transpose l)b),  (1)
```

for nonzero `a,b in F_2^3`, where `M` has order seven.  The nonzero orbit of
`a` spans `F_2^3`, as does the dual orbit of `b`.  This proves `(ICF2)`.

The `p_k` commute.  Simultaneous Fourier diagonalization identifies their
joint spectrum with the dual vector space `F_2^3`.  Conjugation by `T`
fixes the zero character and acts transitively on the seven nonzero
characters.  Therefore the only `T`-fixed projections in `A_p` are

```text
0,        r_0,        r_*=1-r_0,        1.            (2)
```

Multiplication by `q_0=Z_b` sends a Fourier label `lambda` to
`lambda+b`.  Since `b!=0`, it sends `0` outside `{0}` and sends `b` into
`{0}`.  Neither proper projection in `(2)` reduces `q_0`, proving `(ICF4)`.
The exchanged argument is identical.  If both rows are required to reduce,
the generated algebra is `M_8(C)`, whose center contains no proper
projection.  This is the group-algebra cut dichotomy.

Here is an exact finite model showing that passing to the full label block
does not identify the gauge.  On

```text
H=C^2_D tensor C^(F_2^3)_label tensor C^2_n             (3)
```

let `D=Z` on the first factor and let the marked reflection `n=Z` on the
last factor.  On `n=-1`, take `C=X_(e_1)` and `q=Z_(e_1)`; on `n=+1`, take
both to be one.  Use the following involutory factorization of the same
Singer stage action:

```text
A=[[1,0,1],[0,1,0],[0,0,1]],
B=[[1,0,0],[0,1,0],[0,1,1]],
J=[[0,1,0],[1,0,0],[0,0,1]].                          (4)
```

on the label.  Attach the central factor `D` to the occurrences of `A` and
`J`, so it cancels in

```text
T=JBA=M^3,                  M^7=1.                    (5)
```

Let `U` be controlled `X_(e_3)` on the marked block and let `V` be
controlled `Z_(e_3)`.  Since

```text
(1+A)e_3=e_1,             (1+B^(-transpose))e_3=e_2, (6)
```

the ordinary unitary commutators give

```text
[U,A]=C=X_(e_1),          [B,V]=q'=Z_(e_2).           (7)
```

The matrix `J` exchanges `e_1,e_2`, so for `q=Z_(e_1)` one has
`JCJ=X_(e_2)` and `JqJ=q'=Z_(e_2)`.  These are the target occurrences of
the naturality diamond.
Their commutator is `n`, which remains nontrivial.  The Singer orbit sums
of every nonzero vector and covector are zero, giving both orbit norm-one
relations.  All orbit operators ignore the first factor in `(3)`, whereas
`D` and `n` are distinct coordinate reflections.  This proves
`(ICF6)--(ICF7)`.

The MSI artifact checks every displayed word as an exact signed
permutation, verifies the order-seven products, computes rank three of the
Pauli pairing, enumerates the two Singer-invariant one-arm cuts, and checks
that all orbit operators are blind to the native-gauge bit.  There is no
numerical tolerance or exhaustive word search.
