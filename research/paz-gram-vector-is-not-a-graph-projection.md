---
rg: 2
id: paz-gram-vector-is-not-a-graph-projection
kind: claim
title: The PAZ Gram vector does not supply a positive-density graph projection
distinct_from:
  graph-commutator-authenticates-paz-return: that proves a correct analytic comparison for a projection and a unitary acting on the same Hilbert space; this shows that the PAZ input is a vector in an adjoint Hilbert space, not such a projection.
  graph-involution-forces-paz-return: that proves a correct conditional two-projection theorem once the graph source is a projection with strict compression; this refutes the claimed exact PAZ realization of that source.
  pauli-zero-atom-removes-acceptance-source-deficit: that gives a dimension-free norm for one Gram vector; this proves that promoting that vector to a projection either dilutes by the adjoint dimension or loses exact return.
---

There are two different ambient types in the PAZ construction.

For a `d`-dimensional matrix strategy, before the fixed control factors are
added the cyclic game compressor acts on

```text
K_d=L^2(M_d,tr_d),                  dim K_d=d^2.        (PGP1)
```

After the fixed control realization is added, the total Gram Hilbert space
has dimension

```text
N_d=c_m d^2                                             (PGP1a)
```

for one constant `c_m` depending only on the static game.  PAZ supplies the
**vector**

```text
g=P_0Q in K_d^(ctl),                                  (PGP2)
||g||^2=2^(-m)tau_d(Q),
```

and `W_game` is a unitary **superoperator** on the Hilbert space in
`(PGP2)`.  The exact perfect witness gives only

```text
W_game g=g.                                           (PGP3)
```

By contrast, the graph calculation in
`graph-commutator-authenticates-paz-return` begins with an orthogonal
projection

```text
mathsf G in End(C^(2^m) tensor K_d)                   (PGP4)
```

and takes normalized operator trace on that endomorphism algebra.  Reusing
the letter `G` for `(PGP2)` and `(PGP4)` does not identify the two objects.

## The rank-one promotion has fatal normalized-trace dilution

The projection canonically supplied by the vector is

```text
e_g=|g><g|/||g||^2.                                   (PGP5)
```

It is compatible with perfect return: `(PGP3)` implies
`W_game e_g=e_g W_game=e_g`.  But, with normalized trace on the full
endomorphism algebra,

```text
Tr_norm(e_g)=1/N_d=Theta_m(d^(-2)).                   (PGP6)
```

This has no lower bound in terms of `2^(-m)tau_d(Q)`.  Common amplification
does not help: `e_g tensor I_k` has normalized trace `1/N_d` again.  Moreover
the graph return energy of `(PGP5)` is the
one-vector return energy divided by the same ambient dimension.  Thus the
rank-one realization converts the desired dimension-free PAZ payment into a
rank-one defect.

## The positive-density promotion loses exact return

There is an obvious positive-density projection:

```text
mathsf G_L=P_0 tensor L_Q,                             (PGP7)
```

where `L_Q(A)=QA`.  Indeed

```text
Tr_norm(mathsf G_L)=2^(-m)tau_d(Q).                   (PGP8)
```

This is exactly the density wanted by PAZ.  But `(PGP3)` says nothing about
the action of `W_game` on the other vectors `QA` in the left ideal.  In
particular it does not imply

```text
W_game mathsf G_L=mathsf G_L                          (PGP9)
```

or the weaker condition needed by the graph cell, namely that the graph
source projection commute with its `W_game`-conjugate.

The same problem affects the two-sided projection `L_QR_Q`, whose normalized
rank is `tau(Q)^2`: the perfect strategy fixes the one vector `Q`, not the
whole corner `QM_dQ`.

## Exact counterexample

Take `K=M_2(C)` with Hilbert--Schmidt inner product, put

```text
g=I,
D=diag(1,omega),
W=Ad_D,                                               (PGP10)
```

where `omega` is a unit complex number different from `+1` and `-1`.  Then

```text
Wg=g                                                   (PGP11)
```

exactly.  Thus the rank-one Gram return is perfect.

For the positive-density choice `mathsf G_L=L_I=I_K`, form the graph
projection and graph comparison unitary exactly as in the graph cell.  Its
overlap compression is

```text
H=(I+W)/2.                                             (PGP12)
```

On the matrix unit `E_12`, `W` has eigenvalue `conj(omega)`, so `H^*H` has
the eigenvalue

```text
|1+omega|^2/4=(1+Re(omega))/2,                        (PGP13)
```

strictly between zero and one.  Hence `H^*H` is not a projection.  By the
two-projection identity used in `graph-involution-forces-paz-return`, the
graph source and its conjugate do not commute, and the graph commutator
`C=ABAB` is not self-adjoint and not an involution.

Therefore the proposed exact relation

```text
C=Y,                      Y^*=Y, Y^2=I                (PGP14)
```

has no extension in this exact perfect-vector model.  Tensoring or countable
amplification only repeats the spectral value `(PGP13)` and does not repair
it.

This is not foreign to the PAZ verifier.  In an exact BCS strategy a
consistency acceptance projection acts by

```text
A -> (A+XAX)/2.                                       (PGP15)
```

It fixes the tracial vector `I`, but it is not the identity on the whole
left ideal.  Products of different consistency acceptors can have the
generic principal-angle spectrum in `(PGP13)`.  Exact perfect acceptance of
the strategy vector therefore does not make a positive-density algebra
module into a perfect subrepresentation of `W_game`.

## Consequence for the graph PAZ claim

The analytic theorems in the two graph nodes remain valid **conditional on**
a projection `(PGP4)` with the stated compression and exact-extension
properties.  What fails is the claim that PAZ already supplies that
projection.

The one-vector quantity

```text
||g||^2-Re <g,W_game g>                               (PGP16)
```

is not the operator-trace quantity

```text
Tr_norm(mathsf G)-Re Tr_norm(mathsf G W_game mathsf G).
                                                               (PGP17)
```

For `(PGP5)`, `(PGP17)` is diluted by `N_d=Theta_m(d^2)`.  For `(PGP7)`, it averages
over the entire left ideal and need not vanish on the exact perfect witness.
Thus `(PAZ13)` has not been obtained from the current graph relation.

## Minimal repaired target

A valid graph promotion would have to construct, by fixed ordinary packet
data, a projection `mathsf G` such that simultaneously

```text
Tr_norm(mathsf G)>=gamma tau(Q),
the exact perfect witness makes C(mathsf G,W_game) an involution,
finite game soundness gives ||mathsf G W_game mathsf G||_op<1,
and mathsf G is named with dimension-independent relator loss.             (PGP18)
```

Neither the Gram vector nor its left support proves `(PGP18)`.  It is a
positive-density coherent-frame/common-module theorem, essentially the
source-saturation problem in projection form.  Without it, the graph trick
does not close PAZ12.
