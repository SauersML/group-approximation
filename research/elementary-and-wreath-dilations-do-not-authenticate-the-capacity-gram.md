---
rg: 2
id: elementary-and-wreath-dilations-do-not-authenticate-the-capacity-gram
kind: claim
title: Elementary Steinberg and finite monomial dilations name the Hecke unitary but do not authenticate its capacity Gram
distinct_from:
  orthogonal-hecke-row-packs-common-source-energy-into-one-root: that packs the desired covariance energy into one coefficient row; this audits two explicit ways of turning its finite Hecke unitary into an ordinary group word.
  global-word-covariance-cannot-replace-the-capacity-gated-hecke-moment: that treats a freely adjoined global conjugator; this treats the stronger exact elementary and monomial realizations of the finite Hecke sum.
  common-source-leavitt-cell-inherits-rectangular-root-escape: that exhibits rectangular escape for a four-child Leavitt row; this locates the surviving escape after the Hecke unitary itself has been transported at equal scale.
---

Let `q` be the selected finite-packet idempotent and let `V in q C[K] q`
be the finite-support Hecke unitary from
`gauge-pair-holonomy-needs-one-source-moment`.  Put

```text
u=V+(1-q).                                               (EWD1)
```

Then `u` is a unit of the finite-support group algebra, with
`u^(-1)=V^*+(1-q)`.  There are two obvious ways to make `u` visible through
ordinary group words: an elementary Steinberg dilation and a finite
wreath/monomial dilation.  Both solve the exact **naming** problem.  Neither
proves the capacity-gated Gram estimate `(OHR6)`.

## Exact fixed-rank Steinberg naming

For every unit `u` in a unital ring, define

```text
w_(12)(u)=x_(12)(u)x_(21)(-u^(-1))x_(12)(u),            (EWD2)
h_(12)(u)=w_(12)(u)w_(12)(-1).                          (EWD3)
```

Under the elementary-matrix quotient these words are

```text
w_(12)(u) |-> [[0,u],[-u^(-1),0]],
h_(12)(u) |-> diag(u,u^(-1)).                           (EWD4)
```

Thus `diag(V+(1-q),V^*+(1-q))` is represented by one fixed-rank
Steinberg word.  The usual Steinberg conjugation formulas transport root
coefficients by left and right multiplication by `u` and `u^(-1)`.

This is a useful exact closure: no new abstract generator is needed, the
word is finite, and the transport by `u` itself is equal scale.  In
particular multiplication by `u` sends a finite coefficient subspace to an
equal-dimensional coefficient subspace.  It would be incorrect to claim
that rectangular label expansion occurs in this unit transport alone.

## Why the word still does not imply `(OHR6)`

An arbitrary unitary representation of `St_n(R)` is not thereby a
`*`-representation of the coefficient ring `R`.  Root words remember the
additive-root law and Steinberg multiplication triangles.  On a fixed finite
root window, Fourier transform can realize those laws as permutations and
shears of additive-character labels without producing operators

```text
pi(q), pi(V), pi(R_Q)                                   (EWD5)
```

on one common multiplicity space.

The capacity source `Q=(1-C)E` is a nonunit projection obtained only after
matrix decoding.  Even an exact word for `h_(12)(u)` does not identify this
analytic `Q` with the coefficient idempotent `q`, nor does it prove that the
root coordinate called `R_Q` has Hilbert--Schmidt norm equal to the concrete
row norm in `(OHR3)`.  That missing assertion is exactly

```text
||R_Q(U)||_2^2
 <= K ||x_(12)(R_Q)(U)-I||_2^2+o(1).                   (EWD6)
```

The rectangular escape therefore moves one layer down: not into the
equal-scale unit `u`, but into the choice of the selected `q/Q` carrier and
its root-Fourier multiplicity reservoir.  A finite root table may transport
its character labels perfectly while enlarging a recovered paired label
space and shrinking its multiplicity.  Formal elementary factorization does
not charge that conversion.

## Finite wreath/monomial realization

There is also an exact representation-level realization of the Hecke sum.
Let

```text
K_D=(C_2)^D semidirect S_D
```

be the signed permutation packet in its natural representation with
coordinate projections `e_1,...,e_D`.  In a finite wreath product
`L^D semidirect K_D`, a base element `b=(l_1,...,l_D)` acts in the standard
imprimitivity representation as

```text
pi(b)=sum_i e_i tensor pi_L(l_i).                       (EWD7)
```

Consequently a finite controlled sum such as `V=sum_i e_i W_i` can indeed
be promoted to one ordinary monomial group element after choosing the
coordinate phases `W_i` in a finite auxiliary group.  This again solves
exact naming in the intended imprimitivity representation.

It does not solve canonical source saturation.  Let `q_D` be the primitive
central idempotent of the natural `D`-dimensional signed-permutation type,
with `D>=3`.  Its character is nonzero on every one-coordinate sign flip and
on every transposition: both character values are `D-2`.  These elements
generate `K_D`.  Hence the support of `q_D` generates the whole packet.

If a base element `b in L^D` preserves the full primitive carrier,

```text
b q_D b^(-1)=q_D,                                      (EWD8)
```

then it normalizes the subgroup generated by the support of `q_D`, namely
`K_D`.  For the coordinate-permutation action this forces

```text
b=(l,l,...,l).                                         (EWD9)
```

Indeed the base component of `b k b^(-1)` is
`b (k dot b^(-1))`; its vanishing for all transpositions says that all
coordinates of `b` agree.  Such a constant tuple acts only as a uniform
external multiplicity operator.  It cannot implement a coordinate-dependent
block-escaping Hecke sum.

Conversely, a nonconstant tuple implements the desired monomial control but
fails `(EWD8)`.  In the canonical/regular packet its compression has a
positive source deficit even at zero defining-relator error.  The wreath
dilation has therefore merely relocated the selected-type/source-saturation
problem; it has not authenticated a common capacity Gram.

The small exceptional natural type `D=2`, for which the displayed character
value vanishes, is irrelevant: the fixed packet can be enlarged to `D>=3`,
and the same support-generation argument applies.

## Exact HALT audit

The elementary word `(EWD3)` is harmless in an exact gauge-covariantized
HALT representation because it is an identity internal to the chosen
coefficient model.  The monomial dilation is likewise harmless **after** an
intended imprimitivity representation has been supplied.  Neither fact
proves that an arbitrary exact HALT context extends to global conjugacy on
the whole selected finite packet: that stronger claim fails for the reasons
in `global-word-covariance-cannot-replace-the-capacity-gated-hecke-moment`.

The capacity-gated row has the correct firewall.  If `Q=0`, its row
coefficient is zero and no packet weights have to be added.  If `Q` survives,
the required finite-dimensional statement is only the scalar authentication
`(EWD6)`.

## Conclusion

The exact algebraic obstacle is no longer the absence of an ordinary word
for the finite Hecke unitary:

```text
Hecke unitary
 -> fixed Steinberg word or finite monomial element       proved.
```

The remaining obstruction is analytic and matrix-coordinate:

```text
one root word
 -> L2 norm of the capacity-gated common-source row       open.   (EWD10)
```

Neither elementary dilation nor finite wreath control weakens `(OHR6)`.
They prove that `(OHR6)` is the exact final interface rather than a symptom
of missing group syntax.
