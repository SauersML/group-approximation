---
rg: 2
id: agent-leavitt-local-spin-corner
kind: claim
title: The marked Leavitt negative corner contains a unital algebraic CAR reservoir, but that reservoir cannot host the fixed non-CE BCS
artifacts:
  - research/agent-leavitt-local-spin-corner-proof.md
distinct_from:
  nine-pair-marked-heisenberg-regularization-is-selector-spectator: that constructs nine pairs using spare root indices, or finitely many coefficient-packed pairs at one common depth; this constructs one nested extraspecial chain of arbitrary rank and identifies its entire negative-corner direct limit.
  agent-leavitt-not-bcs-negative-root-corner: that asks for the non-CE BCS algebra in the full noncentral Hecke corner; this proves that the most immediate arbitrarily large matrix reservoir inside that corner is locally finite and therefore cannot receive that algebra.
---

**ESTABLISHED.**  Put

```text
R=L_(F_2)(1,2),          Delta=St_20(R),
q=s_1t_1,                z=x_13(q),
P=(1-z)/2 in C[Delta].                                  (ELP1)
```

For every `d>=1`, `Delta` contains an extraspecial group `E_d` of order
`2^(1+2d)` whose center is exactly `<z>`.  These groups may be chosen nested,
and

```text
P C[E_d] P ~= M_(2^d)(C)                               (ELP2)
```

as unital star subalgebras of `P C[Delta] P`, with common unit `P`.
Consequently the full negative corner contains a unital copy of the
algebraic dyadic CAR algebra

```text
M_2(C) -> M_4(C) -> M_8(C) -> ... ,
             T |-> T tensor I_2.                       (ELP3)
```

This does **not** solve `agent-leavitt-not-bcs-negative-root-corner`.
Indeed, no unital star homomorphism from `A(B_loop)` can land in the
subalgebra `(ELP3)`: finite generation would put its image in one matrix
stage, and normalized matrix trace would then pull back to a
Connes-embeddable tracial state on `A(B_loop)`.  The fixed BCS has no such
state.  Thus arbitrarily large full matrix blocks are present, but a
successful BCS map must use elements outside every locally finite spin
reservoir of this kind.

## Construction of the nested extraspecial groups

Choose an infinite prefix-free family of nonempty binary words, for example

```text
alpha_i=0^(i-1)1,                 i=1,2,... .           (ELP4)
```

Prefix cancellation gives

```text
t_(alpha_i)s_(alpha_j)=delta_(i,j)1.                   (ELP5)
```

Define coefficients and Steinberg roots

```text
a_i=s_1t_(alpha_i),               b_i=s_(alpha_i)t_1,
X_i=x_12(a_i),                    Y_i=x_23(b_i).        (ELP6)
```

Then

```text
a_i b_j=delta_(i,j)q.                                  (ELP7)
```

The defining Steinberg relations, all internal to the three root positions
`12,23,13`, now give

```text
X_i^2=Y_i^2=z^2=1,
[X_i,X_j]=[Y_i,Y_j]=[z,X_i]=[z,Y_i]=1,
[X_i,Y_j]=z^(delta_(i,j)).                              (ELP8)
```

(The possible sign in the usual `A_2` commutator formula disappears in
characteristic two.)  Therefore

```text
E_d=<z,X_1,...,X_d,Y_1,...,Y_d>                        (ELP9)
```

is a quotient of the plus-type extraspecial presentation.  It remains to
check that no unintended Steinberg-kernel relation shrinks this quotient.

Use the canonical map

```text
pi:St_20(R) -> E_20(R).                                (ELP10)
```

Every element of the presented group has a normal form

```text
z^e product_i X_i^(u_i) product_i Y_i^(v_i),
e,u_i,v_i in F_2.                                      (ELP11)
```

Its image under `pi` has `12`- and `23`-entries

```text
A=sum_i u_i a_i,                    B=sum_i v_i b_i.   (ELP12)
```

The `a_i` are linearly independent: multiplying `sum_i u_i a_i=0` on the
left by `t_1` and on the right by `s_(alpha_j)` returns `u_j=0` by `(ELP5)`.
Likewise, multiplication of `sum_i v_i b_i=0` on the left by
`t_(alpha_j)` and on the right by `s_1` returns `v_j=0`.  Hence an element
in `(ELP11)` can map to the identity only after all `u_i,v_i` vanish.  Its
remaining `13`-entry is then `e q`, which vanishes only for `e=0`, since

```text
t_1 q s_1=1.                                           (ELP13)
```

Thus all `2^(1+2d)` normal forms are distinct already in `E_20(R)`, and
therefore also in `Delta`.  This proves that `E_d` is extraspecial, that its
center and commutator subgroup are both `<z>`, and that the inclusions
`E_d subset E_(d+1)` are literal.

## The negative group-algebra block

Inside `C[E_d]`, `z` is central and `P=(1-z)/2` is the negative central
idempotent.  Choose the `2^(2d)` coset representatives

```text
r_(u,v)=product_i X_i^(u_i) product_i Y_i^(v_i).       (ELP14)
```

The elements `P r_(u,v)` are linearly independent: in the group basis each
is `(r_(u,v)-z r_(u,v))/2`, and these pairs of basis elements are disjoint.
They also span `P C[E_d] P`.  Hence

```text
dim_C(P C[E_d]P)=2^(2d).                               (ELP15)
```

On `(C^2)^(tensor d)`, send `z` to `-I`, each `X_i` to Pauli `Z` in tensor
slot `i`, and each `Y_i` to Pauli `X` in tensor slot `i`.  Relations
`(ELP8)` hold, and the images of the representatives `(ELP14)` are the
`4^d` tensor-Pauli matrices, which are linearly independent (equivalently,
orthogonal for the Hilbert--Schmidt inner product).  The induced map

```text
P C[E_d]P -> M_(2^d)(C)                               (ELP16)
```

is therefore an isomorphism by `(ELP15)`.  Since `E_d` is an actual subgroup
of `Delta`, the group-basis inclusion `C[E_d] subset C[Delta]` is injective;
thus `(ELP16)` identifies a genuine subalgebra of the ambient Hecke corner,
not merely a quotient.  Its unit is `P`, the unit of `P C[Delta]P`.

The inclusions between successive blocks are unital.  The unique negative
spin representation of `E_(d+1)`, restricted to `E_d`, is two copies of the
negative spin representation of `E_d`; under tensor-Pauli coordinates the
connecting map is exactly `T |-> T tensor I_2`.  This proves `(ELP3)`.

## Why the degree-zero finite core does not already prove this

The first pair in `(ELP6)` is degree zero, but for `i>=2`

```text
deg(a_i)=1-|alpha_i|=1-i,       deg(b_i)=i-1.          (ELP17)
```

Thus arbitrary rank crosses the degree-zero fence.  This is consistent with
`degree-zero-leavitt-core-has-locally-finite-marked-models`: a fixed
balanced-prefix inventory lies in one finite coefficient matrix ring.  The
nine-pair construction using spare root indices stays degree zero but is
bounded by the fixed rank-twenty root geometry.  Here the nonzero gauge
degrees supply infinitely many mutually orthogonal coefficient channels,
while the subgroup itself remains finite at every stage because `(ELP8)`
closes it exactly.

## Exact obstruction for the fixed BCS

Let

```text
U=union_d P C[E_d]P.                                   (ELP18)
```

If a unital star homomorphism `Phi:A(B_loop)->U` existed, the finite set of
BCS generators would have images in one common nested stage
`P C[E_d]P~=M_(2^d)(C)`.  Composing `Phi` with normalized matrix trace would
give a tracial state on `A(B_loop)` factoring through a matrix algebra, hence
a Connes-embeddable tracial state.  This contradicts
`lin-explicit-fixed-bcs-gap-via-generic-conversion` and the BCS trace
dictionary used by `agent-leavitt-not-bcs-corner-closes-full-radical`.

Therefore the matrix-block assertion is true in its strongest natural
nested form, but it is not the missing occurrence-typing step.  A solution
of the full corner gate must mix the spin reservoir with group-ring support
outside `U` in a way that destroys the finite-stage trace without destroying
the BCS projection relations.
