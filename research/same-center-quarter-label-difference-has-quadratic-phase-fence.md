---
rg: 2
id: same-center-quarter-label-difference-has-quadratic-phase-fence
kind: claim
title: The first same-center label difference is quadratic and is not a native Pauli--Whitehead word
artifacts:
  - research/same-center-quarter-label-difference-quadratic-phase-proof.md
distinct_from:
  same-center-m8-commutators-cannot-wordize-one-eighth-reflection: that uses odd determinant to fence the second one-eighth row; the first quarter row has determinant one, and this proves its separate affine-versus-quadratic obstruction.
  shared-gauge-cz-cancellation-needs-an-identity-outer-anchor: that classifies repeated occurrences of one CZ covariance letter; this identifies the exact desired first label-difference word and proves it is absent from the literal same-center Pauli--Whitehead actor group.
  monomial-central-sign-has-types-or-affine-returns: that gives a general finite monomial dichotomy; this computes the native three-qubit label image and its failure on the specific `C_(1/4) SWAP_(1,2)` occurrence required by the selector compiler.
  binary-leavitt-two-label-difference-occurrence-cells: that asks for two new literal occurrence cells; this closes the internal-word search for its first cell and isolates the additional cross-outer gauge equation any external CZ occurrence must satisfy.
---

**ESTABLISHED SCOPED FENCE.**  On the common carrier of
`same-center-prefix-whiteheads-are-uncontrolled-adjacent-swaps`, use the
standard label basis

```text
|x_1,x_2,x_3>,                  x_i in F_2,             (QLD1)
```

in which the six literal root occurrences `A_m,B_m` are the three Pauli
pairs and the literal prefix Whiteheads `J_1,J_2` act by the adjacent qubit
swaps.  Every label word in

```text
G_native=<A_1,B_1,A_2,B_2,A_3,B_3,J_1,J_2>            (QLD2)
```

therefore has the monomial form

```text
|x> |-> (-1)^(c+a dot x) |pi(x)+b>,                    (QLD3)
```

for `a,b in F_2^3`, `c in F_2`, and a coordinate permutation
`pi in S_3`.

For the nested dyadic selector convention, the quarter reflection is the
two-bit controlled sign

```text
C_(1/4)|x>=(-1)^(x_1 x_2)|x>.                          (QLD4)
```

Consequently the first label difference required by
`binary-leavitt-two-label-difference-occurrence-cells` acts as

```text
C_(1/4) SWAP_(1,2)|x>
  =(-1)^(x_1 x_2)|x_2,x_1,x_3>.                        (QLD5)
```

This is not of the form `(QLD3)`.  Equality of the basis permutation would
force `b=0` and `pi=(1,2)`, after which equality of phases would say that
the quadratic Boolean function `x_1x_2` is affine.  Its four-point second
difference is one, while every affine function has second difference zero.
Thus

```text
C_(1/4) SWAP_(1,2) notin label(G_native).              (QLD6)
```

In particular there is no ordinary word built only from the actual six
same-center Pauli root occurrences and the two actual prefix-Whitehead
words which can serve as the label-only `L_1` cell.  This conclusion is
unaffected by arbitrary reservoir factors on the `J_i`: the label action is
already impossible.

The determinant test does not see this obstruction.  Both
`C_(1/4)` and `SWAP_(1,2)` have a two-dimensional negative eigenspace in
dimension eight, hence determinant one.  The second row is fenced by odd
determinant, but the first row is fenced by quadratic phase.

There is one precise way to leave `(QLD6)`.  If a new ordinary root/Clifford
occurrence `K` authenticates the controlled-Z covariance, finite Pauli
representation theory gives on the common carrier

```text
K=C_(1/4) tensor D,             J_1=SWAP_(1,2) tensor V_1, (QLD7)
```

with multiplicity unitaries `D,V_1`.  Then

```text
KJ_1=(C_(1/4) SWAP_(1,2)) tensor D V_1.                (QLD8)
```

Hence this external occurrence supplies the required label-only `L_1`
exactly only if the same literal packet also authenticates

```text
D V_1=I_M.                                             (QLD9)
```

Covariance of `K` and covariance of `J_1` do not imply `(QLD9)`: they are
different outer actions of the Pauli packet and retain independent
multiplicity data.  Packet dressing can share a gauge only within one outer
class.  Therefore an external CZ word is useful only together with a new
cross-outer occurrence relation coupling its actual reservoir gauge to the
actual first Whitehead gauge.  Naming the CZ covariance alone does not
authenticate `L_1`.

This fence is deliberately scoped.  It excludes the complete internal
search in the established same-center Pauli--Whitehead actor packet; it does
not exclude a genuinely scale-changing nonnormal root occurrence which
proves `(QLD9)`.  No Property `(T)`, canonical trace, stability theorem, or
literature input is used.

DERIVATION
same-center-quarter-label-difference-quadratic-phase-proof
