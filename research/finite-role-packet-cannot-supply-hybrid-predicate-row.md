---
rg: 2
id: finite-role-packet-cannot-supply-hybrid-predicate-row
kind: claim
title: A finite role packet cannot supply a universally oriented hybrid predicate row
distinct_from:
  sectorwise-scalar-finite-group-words-are-selector-affine: that assumes a central selector subgroup and classifies words scalar on its marked irreducibles; this uses the finite regular representation, allows a noncentral selector subgroup, includes the D8 role swap, and gives an explicit normalized-HS gap for the hybrid row.
  finite-selector-gadget-induction-barrier: that proves every selector character occurs in some marked representation; this proves that an ordinary word correct on all those character spaces must itself be a selector word.
  dihedral-spin-packet-supplies-common-partial-swap: that constructs the common D8 partial source and isolates the hybrid row as the remaining compiler problem; this rules out solving that problem by a universally saturated finite packet, including a role-covariant commutator circuit.
  controlled-pauli-commutator-is-and-times-multiplicity-commutator: that isolates the external multiplicity commutator left by two controlled gates; this proves that even perfect cancellation of that commutator cannot produce the required universal hybrid row inside one finite packet.
  shared-multiplicity-commutator-builds-selected-hybrid-row: that deliberately does not cancel the common external factor inside the row; the final D8 swap commutator cancels it and constructs the hybrid test on one selected type.
---

Let `H` be a finite group, let

```text
y in Z(H),                 y^2=1,                      (FRP1)
```

and let

```text
A=<y,z,a_1,...,a_k> <= H                               (FRP2)
```

be an elementary abelian two-subgroup.  The generator `z` is the D8 role
bit.  A common swap `j` is allowed to lie anywhere in `H`; in the intended
application it satisfies

```text
j^2=1,                    [z,j]=y.                    (FRP3)
```

The subgroup `A` is not assumed central in `H`.

For each character `chi in dual(A)` with `chi(y)=-1`, let

```text
p_chi=1/|A| sum_(a in A) conjugate(chi(a)) a.          (FRP4)
```

Put `p_-=(1-y)/2=sum_(chi(y)=-1)p_chi`.

## Regular-sector rigidity

### Theorem

Suppose `e in H` has the following property in every finite-dimensional
unitary representation of `H` on which `y=-I`: on the `chi`-weight space of
`A`, the operator `e` is a prescribed scalar `epsilon_chi in {+1,-1}`.
Then

```text
e in A,                                                     (FRP5)
epsilon_chi=chi(e).                                         (FRP6)
```

In particular the sign table `chi -> epsilon_chi` is an affine character of
the selector bits.

It is enough to assume the displayed property on the `y=-1` part of the
left regular representation of `H`.

### Proof

Apply the hypothesis to the left regular representation on `p_- C[H]`.
The `chi`-weight space is the range of left multiplication by `p_chi`, so

```text
e p_chi=epsilon_chi p_chi.                              (FRP7)
```

Summing over the marked characters gives

```text
e p_-=sum_(chi(y)=-1) epsilon_chi p_chi in C[A].       (FRP8)
```

But

```text
e p_-=(e-ey)/2.                                        (FRP9)
```

If `e` were outside `A`, then the two distinct group-basis elements `e,ey`
would both lie outside `A`; their coefficients in `(FRP9)` could not cancel
against an element supported on `A`.  Thus `e in A`.  Equation `(FRP6)` is
then ordinary character evaluation.  No centrality of the other selectors
was used.  QED.

## The hybrid row has a fixed regular-packet gap

Write the marked characters as `(r,x)`, where

```text
chi(z)=(-1)^r,                 r in {0,1},
chi(a_i)=(-1)^(x_i).                              (FRP10)
```

For a Boolean predicate `f`, the D8 compiler asks for the role-labelled
truth table

```text
epsilon_f(0,x)=(-1)^(f(x)),
epsilon_f(1,x)=+1.                                   (FRP11)
```

Equivalently, the requested row is

```text
E_f=diag(1-2F_f(A), I)                                (FRP12)
```

on the common `y=-1` role spin.

No nontrivial table `(FRP11)` is a character.  Indeed a character which is
`+1` for every `(1,x)` has zero coefficient on every selector and on the
role bit, and is therefore also `+1` for every `(0,x)`.  Theorem `(FRP5)`
therefore rules out `(FRP12)` for every predicate which rejects at least one
assignment, not merely for predicates of algebraic degree at least two.

There is a quantitative version.  Define the group-algebra hybrid reflection

```text
q_f=sum_(chi(y)=-1) epsilon_f(chi) p_chi in p_- C[A]. (FRP13)
```

For the normalized regular trace `tau_H` and every `e in H`,

```text
||p_-(e-q_f)||_(2,tau_H)^2
 >= 4/|A|                                              (FRP14)
```

unless `(FRP11)` is exactly a character.  If `e` is outside `A`, the two
summands have disjoint group-basis support and the squared distance is `1`.
If `e` lies in `A`, both are diagonal on the marked character atoms and

```text
||p_-(e-q_f)||_2^2
 =4/|A| * #{chi(y)=-1 : chi(e)!=epsilon_f(chi)}.       (FRP15)
```

The mismatch set is nonempty by the preceding paragraph, proving `(FRP14)`.
Thus the obstruction is already at fixed normalized-HS scale in the exact
finite regular packet; it is not a small exceptional character.

## The row exists exactly in the group algebra

The theorem separates a group-word obstruction from a logical one.  Put

```text
p_(z,+)=(1+z)/2,                  p_(z,-)=(1-z)/2,
p_x=product_i (1+(-1)^(x_i)a_i)/2,
h_f=sum_x (-1)^(f(x)) p_x.                           (FRP16)
```

Then the finite rational group-algebra element

```text
Q_f=p_(z,+) h_f+p_(z,-)                              (FRP17)
```

is a self-adjoint involution and has exactly the hybrid action `(FRP11)` in
every representation, with no selected-type ambiguity.  Thus the D8 row is
already compiled at the finite algebra level.  What is impossible is
replacing `Q_f` by one ordinary group-basis element while retaining that
universal action.

This narrows the positive repair further: one may keep the common D8 swap
and seek a finite-dimensional-only wordization or corner-return for the one
explicit dyadic reflection `(FRP17)`.  Such a mechanism must not assert
`Q_f=e` as a universal group-algebra identity, because `(FRP14)` proves that
no finite packet word can satisfy it.

## Common-swap commutator circuits do not evade the theorem

Consider the proposed repair in which upper and lower gate implementers are
made role-covariant through the common swap `j`.  On a selected finite type,
Schur factorization writes the gates as fixed packet matrices tensored with
external multiplicity unitaries.  Cross-commutator relations may make the
upper and lower gates share those multiplicity unitaries, and balanced words
may even cancel every external multiplicity commutator exactly.

If the resulting ordinary word `e` then has the universal action `(FRP11)`
on the whole marked role spin, it satisfies the hypothesis of the theorem
and hence lies in `A`.  The desired nontrivial hybrid table is impossible.
The common swap can align multiplicity; it cannot turn an ordinary group
basis element into the nonlinear spectral sum `(FRP13)`.

This also identifies the precise limit of the controlled-commutator idea.
For gates

```text
U=C_U tensor R,                V=C_V tensor T,          (FRP18)
```

an extra covariance row can in principle pay or cancel `[R,T]`.  After that
cancellation the remaining finite constant is still one ordinary word of
the finite packet, so `(FRP5)` applies.  Multiplicity-commutator cancellation
is necessary for a selected-type circuit but is not a source-saturation
theorem.

## Gauge doubling and the derived lift

Gauge doubling replaces every logical selector by two commuting shares and
evaluates `f` on their products.  Enlarge `A` in `(FRP2)` by all shares.  The
desired table becomes

```text
epsilon_f(0,a,b)=(-1)^(f(a_1b_1,...,a_kb_k)),
epsilon_f(1,a,b)=+1.                                  (FRP19)
```

The same lower-role argument shows that every character agreeing with
`(FRP17)` is trivial, so any nontrivial predicate is again impossible as one
universally oriented word.  The gauge flip symmetry remains extremely useful
for exact covariantization, and the equal-scale derived lift correctly turns
the reset translation into a legal next-packet phase.  Neither changes the
regular-sector support calculation `(FRP8)--(FRP9)`.

Consequently the derived lift can transport an **oriented selected type**;
it cannot promote that type to a universally scalar row on the entire D8
spin without an additional source/return theorem.

## Exact frontier

The finite D8 compiler now has a sharp dichotomy.

```text
common D8 swap source                         solved;
common literal variable names                 compatible;
universal ordinary-word hybrid predicate row  impossible in a finite packet;
selected non-scalar predicate carrier         available from Schur/Hecke data;
promotion of that carrier to the common source open.                 (FRP20)
```

A viable repair must therefore keep at least one feature absent from this
theorem:

1. use a selected non-scalar finite type and prove that the common source is
   saturated by it;
2. use a group-algebra/Hecke row and a genuinely finite-matrix return which
   promotes its corner moment;
3. use an infinite actuator whose soundness is not a universal identity in
   the packet regular representation; or
4. replace literal row equality by a joint energy inequality which remains
   valid after summing all marked packet types.

Merely adding more finite role-covariant reversible gates, even with perfect
external-multiplicity cancellation, cannot close the row.

There is one important projective loophole, and it is constructive rather
than a gap in the theorem.  The D8 soundness test is invariant under a common
unitary factor on the two role blocks.  Thus it is enough to produce

```text
e=diag(h_f,I) tensor V                                (FRP21)
```

with arbitrary `V`, not the scalar row `(FRP12)` itself.  The present theorem
does not rule out `(FRP21)` because `e` is not scalar on selector-weight
spaces.  `shared-multiplicity-commutator-builds-selected-hybrid-row` realizes
exactly this loophole on one selected finite type.  What remains open is
promotion of that selected carrier, not its role orientation.

## Attempts and firewalls

- **Use `j` inside the final balanced word.**  If the word is scalar on every
  marked `A`-weight, `(FRP8)` still forces it into `A`; `j` disappears rather
  than supplying role localization.
- **Use a finite derived/wreath lift.**  It repairs abelianization and can
  match restriction multiplicities, but its finite regular representation
  is still the witness used in `(FRP7)`.
- **Select only the central sign `y=-1`.**  The whole marked regular sector is
  exactly what produces every character simultaneously.  A primitive
  selected-type projection is extra data, not a consequence of the central
  sign.
- **Claim this rules out every group compiler.**  It does not.  Infinite
  incidences can exclude or return finite packet types, and finite-dimensional
  matrix-only inequalities need not hold in the regular representation of
  the final group.  The theorem rules out the proposed finite packet as the
  complete source-saturated row compiler.
