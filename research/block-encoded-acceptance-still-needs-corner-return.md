---
rg: 2
id: block-encoded-acceptance-still-needs-corner-return
kind: claim
title: Fresh control qubits block-encode the acceptance compressor, but its return is still one Hecke corner moment
distinct_from:
  finite-game-gap-makes-the-cyclic-acceptance-compressor-strict: that constructs the nonunitary strict contraction as a product of acceptance projections; this realizes that product as one exact corner of one fixed unitary.
  cyclic-acceptance-root-needs-kernel-reflection: that packages the additive return difference into one Steinberg coefficient; this avoids the additive sum at the naming level and locates the surviving compressed-corner obstruction.
  hecke-dilations-do-not-lock-capacity-gram: that audits a finite wreath realization of a block-escaping Hecke unitary; this uses the same exact naming technology and proves that the analytic source-deficit problem remains.
---

Let `L_1,...,L_m` be the fixed game rejection projections acting on the Gram
Hilbert space `K`, and put

```text
Q_j=I-L_j,
R_j=I-2L_j,
T_game=Q_m...Q_1.                                     (BAE1)
```

Every `R_j` is a self-adjoint unitary.  Give the `j`-th test its own control
qubit, let `H_j` be the Hadamard on that qubit, and define

```text
B_j
 =H_j [ |0><0| tensor I + |1><1| tensor R_j ] H_j.    (BAE2)
```

Relative to that qubit,

```text
B_j=[[Q_j,L_j],[L_j,Q_j]],                             (BAE3)
```

and `B_j` is a self-adjoint unitary.  On

```text
A=(C^2)^(tensor m),
P=|0^m><0^m| tensor I_K,
W_game=B_m...B_1,                                     (BAE4)
```

we have the exact block identity

```text
P W_game P
 =|0^m><0^m| tensor T_game.                            (BAE5)
```

Indeed each control qubit is touched exactly once.  In a matrix element from
`0^m` back to `0^m`, the `j`-th qubit must therefore take the `0->0` block
`Q_j`; no path which leaves that qubit can return later.  The system blocks
remain in their original order, giving `(BAE5)` even though the `Q_j` do not
commute.

This fresh-control point is essential.  Reusing one control qubit creates
additional paths which leave and return to zero, so its `(0,0)` block is not
the product in `(BAE1)`.

## Exact finite group naming

For a consistency test,

```text
R_(c,x)(G)=A_(c,x)G B_x,                              (BAE6)
```

which is the ordinary two-copy word `A_(c,x) tensor conjugate(B_x)` under
vectorization.  For a predicate test, `R_c=I-2F_c` is the fixed truth-table
reflection of the commuting context packet.  It can be named in the intended
finite monomial/hyperoctahedral packet.  The controlled unitary in `(BAE2)`
is a base element of a two-coordinate wreath product, and `H_j` belongs to a
fixed one-qubit Clifford packet.

Consequently, after one fixed finite ancillary extension, every `B_j` and
their product `W_game` have an exact ordinary group-word realization in the
intended imprimitivity/two-copy representation.  The ancillary dimension
`2^m` is fixed by the one static game.

This sentence concerns the **intended** representation.  It is not a
universal marked-spin statement.  As proved in
`controlled-reflection-cell-has-free-orientation`, the minimal wreath cell
allows an extra multiplicity involution `u_j` in front of each `Q_j`, and the
character twist `c_j->-c_j` preserves the Pauli sign and every control
relation.  A Hecke orientation selection is therefore required before an
arbitrary marked packet model satisfies `(BAE5)`.

Simply doubling each visible controller does not remove this requirement at
the ordinary-word level.  By
`doubled-controllers-do-not-preserve-game-gap`, the zero-control block of
`(c_jH_j)^2` is `w_jQ_j`, where `w_j` is an arbitrary unitary preserving the
accepted subspace.  Such interleaved rotations can make the dressed cyclic
product have operator norm one even when the undressed game compressor has a
fixed strict gap.  The orientation-free construction survives only as the
nonunitary Hecke product of conjugated control projections.

For a Gram vector `G`, write

```text
iota(G)=|0^m> tensor vec(G).                           (BAE7)
```

Then `(BAE5)` gives exactly

```text
||(P W_game P-P)iota(G)||
 =||T_game(G)-G||_2.                                  (BAE8)
```

Thus block encoding removes the additive expansion `(CAP17)` from the
**naming** problem.

## The one corner-return scalar

Let `Q` now denote the actual marked/capacity source and let `U` be a proposed
transport into the zero-control carrier.  Put

```text
S=P U Q,
s=||S||_2^2=tau(Q U^* P U Q).                         (BAE9)
```

The source deficit is

```text
tau(Q)-s=||(I-P)UQ||_2^2.                             (BAE10)
```

The smallest state-local return moment is

```text
eta_ret(S)
 =s-Re tau(S^* W_game S).                             (BAE11)
```

Because `S=PS`, `(BAE5)` and the strict contraction
`||T_game||<=rho<1` give

```text
eta_ret(S)>=(1-rho)s.                                 (BAE12)
```

Also

```text
||(P W_game P-P)S||_2^2<=2 eta_ret(S),                (BAE13)
```

since `||P W_game P S||_2<=||S||_2`.  Hence the desired
capacity-gated cycle return can be reduced to the two scalars

```text
tau(Q)-||PUQ||_2^2,
||PUQ||_2^2-Re tau(Q U^*P W_game P UQ).               (BAE14)
```

The second is the promised one corner-return scalar; the first is the
unavoidable source-saturation scalar.

## Why an HNN/global word does not force `(BAE11)`

A global relation

```text
W_game U=U                                             (BAE15)
```

with unitary `U` implies `W_game=I`.  That is much stronger than fixing the
single perfect Gram vector and is incompatible with the nontrivial verifier
unitary.  The exact perfect witness only satisfies

```text
W_game iota(I)=iota(I),                                (BAE16)
```

not that `W_game` is the identity on its whole representation.

The legal target is therefore the compressed equation

```text
P W_game P UQ approx P UQ.                            (BAE17)
```

But `(BAE17)` is precisely `(BAE11)--(BAE14)`, a mixed Hecke-corner moment.
An ordinary HNN stable letter is unitary on the whole Hilbert space and does
not express this state-local relation.

The source issue has not disappeared either.  Before the return can charge
marked mass, `(BAE10)` must be small.  This is the same selected-carrier
source-Gram saturation problem as `(CSG4)`, now with the zero-control block
`P` as target.  If one instead chooses `G` directly inside `P`, its norm must
still be tied to the analytic marked source by a mixed moment; a fixed
ancilla coordinate alone does not do that.

## Finite wreath no-go survives

The finite wreath product correctly names every controlled unitary in
`(BAE2)`.  It does not authenticate the analytic cut `Q` as the zero-control
coordinate in an arbitrary canonical matrix microstate.  Tensor the exact
ancilla/wreath model with the D8 capacity cut

```text
Q_D8=(I+X)/2                                           (BAE18)
```

from `canonical-root-coordinate-is-binary-not-an-l2-authenticator` and
rotate the independent D8 factor relative to `P`.  All block-encoding and
finite wreath relations remain exact, while the source deficit `(BAE10)` can
take any permitted projection-overlap value.  The verifier corner and the
capacity source occupy independent multiplicity reservoirs.

This is the same mechanism as the support-generation no-go in
`hecke-dilations-do-not-lock-capacity-gram`: a nonconstant controlled base
element names the intended block action, but canonical primitive-carrier
preservation/source saturation does not follow.  The block encoder has moved
the additive difficulty into `(BAE14)`; it has not removed the mixed
same-reservoir theorem.

## Precise gain and remaining target

The construction proves

```text
finite additive acceptance sum
 -> one fixed ordinary unitary W_game and one fixed corner P.  (BAE19)
```

It is therefore a genuine syntax improvement over the Steinberg expansion
`(CAR2)`.  A complete backend would now need only a matrix-only word/two-cell
estimate

```text
tau(Q)-||PUQ||_2^2 + eta_ret(PUQ)
 <=K E_rel+o(1).                                      (BAE20)
```

Together with `(BAE12)` and a lower bound on `tau(Q)`, `(BAE20)` pays the
marked mass immediately.  Neither ordinary HNN covariance nor finite wreath
exactification proves `(BAE20)`; it is exactly the remaining capacity-gated
corner-return theorem.

There is one important specialization.  If the fresh controls are realized
inside the unique marked spin type of an extraspecial Pauli packet and the
original source commutes with the full control packet, then
`pauli-zero-atom-removes-acceptance-source-deficit` takes `G=P_0Q` directly
and proves `||G||_2^2=2^(-m)tau(Q)` (up to fixed packet-rounding error).  In
that model `(BAE10)` is unnecessary: only the corner-return scalar
`eta_ret(P_0Q)` remains open.
