---
rg: 2
id: projective-natural-source-separation-proof
kind: route
title: Decompose the natural projective-head permutation module into signed subgroup orbits
target: projective-star-profile-has-zero-hecke-source
requires:
  - full-q-a1-projective-head-is-a-literal-finite-subgroup
  - marked-root-star-carries-three-anchored-cells
---

Use the seven active labels

```text
(q2,q4,q5,q6,u1,u2,u3)
```

from the projective matrix-unit lift.  Let `X=F_2^7-{0}` and let
`pi_7` be the permutation representation of `SL_7(F_2)` on `C[X]`.
The twelve pattern transvections generate `K` of order `2^15`; its character
`chi` is negative on the first three chain roots

```text
q5->q6, q4->q5, q2->q4
```

and positive on the other nine pattern roots.

For a finite group `A` acting on a finite set and a sign character `eta`,
the rank of the signed average

```text
e_(A,eta)=|A|^(-1)sum_(a in A)eta(a)a
```

on the permutation module is the multiplicity of `eta` in `C[X]`.  On an
orbit `A/Stab(x)` this multiplicity is one exactly when `eta` is trivial on
`Stab(x)`, and is zero otherwise.

Exact row reduction gives the following `K`-orbit representatives and
sizes (vectors are encoded by their seven-bit hexadecimal values):

```text
representative:  01 02 04 08 10 11 12 20 22 30 32 40 44 60
orbit size:       1  2 16 64  1  1  2  2  2  2  2  8 16  8. (1)
```

Every stabilizer in `(1)` contains a `chi`-negative element.  For all
representatives except `08`, the negative transvection with row tuple

```text
(01,02,04,0c,10,20,40)
```

fixes the representative; for `08`, use the negative transvection

```text
(01,02,06,08,10,20,40).                               (2)
```

The orbit sizes in `(1)` sum to `127`, so `(2)` exhausts the permutation
module and proves

```text
rank pi_7(F)=0.                                        (3)
```

For `C_1=q2->q4`, exactly `63` nonzero vectors are fixed.  Its permutation
therefore has `(127-63)/2=32` two-cycles, proving

```text
rank pi_7((1-C_1)/2)=32.                               (4)
```

The three commuting star roots are

```text
q2->q4, q2->q5, q2->q6.
```

Their signed `C_2^3` character occurs precisely when the three target bits
are all one.  The remaining four bits are free, and each compatible orbit
has size two.  Hence there are `16/2=8` compatible orbits and

```text
rank pi_7(E)=8.                                        (5)
```

If either projection in `(4)--(5)` belonged to the two-sided ideal generated
by `F`, its image under every representation would vanish whenever the image
of `F` vanished.  Equations `(3)--(5)` therefore prove both exclusions in
`(PNS3)` for the containing `SL_7` group, and hence also for `P_A` because
the same representation restricts to it.

Finally `J_1,J_2` permute only `u1,u2,u3`, whereas the three star roots use
only `q2,q4,q5,q6`.  Thus they commute with `E`, and

```text
(EJ_1J_2E)^*(EJ_1J_2E)=E,                             (6)
```

which proves `(PNS4)` without computation.

There is also a conceptual certificate which both avoids orbit enumeration
and includes the mark.  In the four chain coordinates write a vector's first
three relevant bits as `(a,b,c)`.  If `a=0`, the first simple chain root
fixes the vector; if `b=0`, the second fixes it; and if `c=0`, the third
fixes it.  Each has negative `chi` sign.  In the remaining case
`a=b=c=1`, the product of the positive derived root `x_52(q)` with the
second negative simple root fixes the vector and still has negative sign.
Thus every vector stabilizer contains a `chi`-negative element.  This proves
directly that the signed `H` average is zero, and hence so are the finer
signed averages `Q` and `F`.

The same derived root also exposes the exact geometric mismatch between the
two proposed sources.  By definition `E` is negative for `x_52(q)`, while
`x_52(q)` is a derived root of the chain group `H` and therefore has positive
`lambda_0` sign on `Q`.  Hence

```text
x_52(q)E=-E,        x_52(q)Q=Q,
EQ=0,               EF=0.                             (6a)
```

Now adjoin the two labels `q@1,q@3`.  The proof of the projective
matrix-unit lift applies verbatim to all nine distinct ambient coordinates
and gives an injective

```text
Phi_9:SL_9(F_2)->Delta.                                (7)
```

It contains the original seven-label head and sends the binary transvection
between `q@1,q@3` to `z=x_13(q)`.  On the `511` nonzero vectors of `F_2^9`,
any transvection fixes the `255` nonzero vectors in an eight-dimensional
hyperplane.  Therefore

```text
rank pi_9(P_z)=(511-255)/2=128.                        (8)
```

The negative-stabilizer argument is unchanged by the two spectator bits, so
`pi_9(F)=0`.  Equivalently, restriction to the old seven-coordinate block
is four copies of the `127`-point permutation module plus three trivial
lines; the signed average vanishes on all seven summands.  For the star
group, the three target bits must again all be
one; the other six bits are free and compatible orbits have size two.  Thus

```text
rank pi_9(E)=2^6/2=32.                                 (9)
```

The commutation in `(6)` gives `rank pi_9(EJ_1J_2E)=32`.  Equations
`(8)--(9)` prove `(PNS3a)` and show that the source separation survives
inside a literal finite subgroup which already contains the marked root.

`experiments/full_q_source_mass_natural_profile_audit.py` independently
enumerates the `32768` pattern elements, verifies the orbit certificate,
and computes all four displayed ranks using integer arithmetic.  It was run
only through the MSI wrapper on `acn112`; no local computation was used.
