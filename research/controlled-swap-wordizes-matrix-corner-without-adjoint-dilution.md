---
rg: 2
id: controlled-swap-wordizes-matrix-corner-without-adjoint-dilution
kind: claim
title: A controlled copy-swap wordizes one matrix-corner return without adjoint dilution
distinct_from:
  paz-gram-vector-is-not-a-graph-projection: that proves the rank-one graph lift of the PAZ Gram vector loses `d^(-2)` and the positive-density module lift loses exact return; this identifies the exact matrix-level actuator which would avoid that loss if the return were an ordinary matrix corner.
  acceptance-return-is-one-corner-word: that isolates the PAZ vector coefficient for a left--right superoperator; this separates the special matrix-multiplication case that is already an ordinary commutator from the genuinely superoperator-valued case.
  controlled-pauli-commutator-is-and-times-multiplicity-commutator: that computes a Pauli-controlled multiplicity commutator after the controlled packet has been supplied; this gives the basis-free two-copy swap identity and audits the minimal switch syntax.
---

Let `(M,tau)` be a finite tracial matrix algebra, let `Q` be a projection,
and let `R` be a unitary commuting with `Q`.  There is an exact two-copy
ordinary-word actuator for the matrix-vector energy

```text
||(R-I)Q||_2^2.                                         (CSW1)
```

It uses no endomorphism algebra of `L^2(M)` and therefore loses no factor of
the matrix dimension.

## The controlled-swap identity

In `M_2(M)` put

```text
A=diag(R,I),
T=[[I-Q,Q],[Q,I-Q]].                                    (CSW2)
```

Then `T=T^*=T^(-1)`.  If `R` is an involution, so is `A`; otherwise `A` is
still unitary.  Define the ordinary commutator word

```text
C=A T A^* T.                                            (CSW3)
```

### Theorem

Exactly,

```text
||C-I||_(2,tau_2)^2=||(R-I)Q||_(2,tau)^2.               (CSW4)
```

Thus a group relator `C=1` pays the complete matrix-corner vector energy at
fixed normalized-HS scale.

### Proof

On `(I-Q)M^2`, the controlled swap `T` is the identity, hence so is `C`.  On
`QM^2`, `T` is the full two-coordinate flip and

```text
A T A^* T=diag(R,R^*).                                  (CSW5)
```

Consequently

```text
||C-I||_2^2
 =1/2( ||(R-I)Q||_2^2+||(R^*-I)Q||_2^2 )
 =||(R-I)Q||_2^2.                                       (CSW6)
```

This is a `2d`-dimensional calculation, rather than a rank-one calculation
inside an algebra of dimension `d^2`.

## Balanced left--right returns are already group words

The same phenomenon appears without an explicit copy switch.  Put
`S=2Q-I`.  For a conjugation return `W(X)=UXU^*`,

```text
||(W-I)Q||_2^2
 =1/4||USU^*-S||_2^2
 =1/4||USU^*S-I||_2^2.                                 (CSW7)
```

The right side is one ordinary commutator-word defect.  Hence conjugation
residuals have no vector/operator type problem.

This does not by itself encode PAZ.  A balanced conjugation fixes the
tracial vector `I` automatically, including on rejecting predicate data.
The finite-game signal uses unbalanced left--right phases and additive
acceptance compression; those are precisely the parts requiring a gated
source.

## The switch is a nonlinear predicate

Although `(CSW4)` is an ordinary word once `T` has been supplied, the formula
for `T` is not a word in the capacity involution and the full copy flip.
Let

```text
S=2Q-I,
K=[[0,I],[I,0]].                                        (CSW8)
```

The three involutions `S,K,T` commute.  On a joint character, the desired
switch rule says

```text
q=0 -> t=0,
q=1 -> t=k,                                             (CSW9)
```

in `F_2` bits.  Its support is

```text
{(q,k,t)}={(0,0,0),(0,1,0),(1,0,0),(1,1,1)}.           (CSW10)
```

This set is not affine: it contains zero, but

```text
(0,1,0)+(1,0,0)=(1,1,0)                                (CSW11)
```

is not allowed.  Relations among commuting involutions cut out only affine
subspaces of their character group.  Therefore no abelian/parity packet can
force the controlled swap.  A nonlinear finite representation type (for
example a Schur or hyperoctahedral predicate packet) is genuinely required.

## Why this still does not graph the PAZ vector

For the PAZ return, `W_game` is a unitary superoperator on
`K_d=L^2(M_d,tr_d)`.  Applying `(CSW2)` on that Hilbert space requires a
positive-density projection such as `L_Q`, and `(CSW4)` then measures

```text
||(W_game-I)L_Q||_(2,End(K_d))^2,                       (CSW12)
```

the average return of the entire left module `QM_d`.  PAZ supplies only

```text
||(W_game-I)Q||_(2,M_d)^2.                              (CSW13)
```

The exact family `W=Ad_D`, `Q=I` from
`paz-gram-vector-is-not-a-graph-projection` has `(CSW13)=0` but
`(CSW12)>0`.  Therefore the controlled swap cannot be applied directly to
the current superoperator return without destroying exact HALT completeness.

The viable use of `(CSW4)` is narrower: first decompose the verifier return
into finitely many ordinary matrix residuals `(R_j-I)Q` on one authenticated
common source, and then use one controlled-swap word for each residual (or a
fixed row pack).  Constructing that common nonlinear switch/source packet is
the remaining source-saturation theorem.

## Attempts

- **Rank-one graph on the PAZ vector.** Loses `d^(-2)` as proved in
  `paz-vector-graph-dimension-loss-proof`.
- **Positive-density left-module switch.** Has the correct finite density,
  but charges vectors that an exact perfect strategy need not fix.
- **Balanced conjugation only.** Gives the exact word identity `(CSW7)`, but
  cannot detect predicate phase on the tracial vector.
- **Commuting-involution switch relations.** Fail by the nonlinear support
  calculation `(CSW9)--(CSW11)`.

## Verdict

There is no intrinsic normalized-HS dilution in a matrix-corner return: the
controlled copy-swap converts it exactly to one commutator word.  The PAZ
obstruction lies one level earlier.  Its return is a superoperator vector
coefficient, and the capacity-controlled swap is a nonlinear, common-source
packet which the current ordinary relations do not authenticate.
