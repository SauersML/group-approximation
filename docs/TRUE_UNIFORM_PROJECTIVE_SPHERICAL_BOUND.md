# A uniform spherical localization threshold for every projective chart

Date: 2026-08-11

## Outcome

For the fixed `SL_3(Z)` cellular resolution used by the projective-chart
program, every degree-three boundary row in every finite permutation
coefficient system satisfies

```text
||row(d_3)||_2^2 <= 52.                                  (USB1)
```

This includes the actions on `P^2(F_p)`, on
`P^2(Z/p^k Z)`, and arbitrary finite coefficient actions.  Consequently the
short-vector localization theorem has the chart-independent implication

```text
||u|| < 1/sqrt(52)  ==>  u is orthogonal to the spherical lattice. (USB2)
```

The observed chartwise bounds `12` and `28` are sharper, but `(USB1)` is a
single uniform theorem and requires no finite-level enumeration.

## Fixed cellular boundary

The HAP complex `ContractibleGcomplex("SL(3,Z)")` has one degree-three cell
and two degree-two cells.  Its degree-three attaching word has ten terms:

```text
target cell 1:  two positive and two negative terms;
target cell 2:  two positive and four negative terms.       (USB3)
```

Thus four terms land in the first target summand and six in the second.
Every term is a group element times a coefficient of absolute value one;
the signed target-cell index records its sign.

The signature `(USB3)` was read from the exact HAP export used for the
level-`121` prime-power complex.  It is data of the fixed integral
resolution, not data depending on the coefficient action or on the level.

## Proof of the bound

Let `e_1,...,e_4` be the signed unit coordinate vectors contributed by the
four terms landing in the first degree-two cell.  Stabilizer coinvariants may
send a term to zero, may change its sign, or may identify its coordinate with
that of another term.  In every case

```text
||e_1+...+e_4||_2 <= 4.                                (USB4)
```

The same argument for the six terms landing in the second cell gives

```text
||f_1+...+f_6||_2 <= 6.                                (USB5)
```

The two target-cell coordinate blocks are orthogonal.  Therefore every
degree-three boundary row has squared norm at most

```text
4^2+6^2=52,                                            (USB6)
```

proving `(USB1)`.

Now let `B` be the maximum norm of a lifted spherical generator in
Proposition 12 of `INTEGRAL_CARRY_DISCRIMINANT_DUALITY.md`.  The selected
degree-three attaching maps generate the spherical subgroup and `(USB1)`
gives `B<=sqrt(52)`.  If `u` belongs to the dual cycle lattice and
`||u||<1/sqrt(52)`, then for every integral spherical generator `sigma`,

```text
|<u,sigma>| <= ||u|| ||sigma|| < 1.                    (USB7)
```

The pairing is integral, hence it is zero.  This proves `(USB2)`.

## Significance and scope

The uniform family question can now use the fixed sufficient screen

```text
lambda_1(Q_X^#) >= 1/sqrt(52)                          (USB8)
```

without first computing a chart-specific spherical norm.  If `(USB8)`
holds, the chart cannot contain a vanishing-denominator class.  A smaller
chartwise value of `B` can still eliminate additional charts, as it does at
levels `61`, `79`, and `89`.

This is a denominator-localization result, not a uniform lower bound on
`lambda_1(Q_X^#)`.  The remaining TRUE problem is to control the paired
integral lifts of the classes which do fall below the uniform threshold.
