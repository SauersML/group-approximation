# STW Problem LXXXI: O-infinity-envelope audit (2026-08-30)

## Exact result

For every nonzero separable C-star algebra `A`, the envelope

```text
E=A tensor O_infinity
```

has no nonzero commutative hereditary subalgebra in any quotient, and

```text
dim_nuc(E)=1       exactly when A is nuclear,
dim_nuc(E)=infinity otherwise.
```

This gives a positive class for Problem LXXXI with arbitrary ideal structure
and no field, local triviality, or base-dimension assumption.  It also shows
that the strongest possible vanishing of the commutative-shadow invariant is
compatible with either nuclear dimension one or infinite nuclear dimension.

## Shadow audit

The only permanence input is standard strong-self-absorption permanence:
for a strongly self-absorbing `D`, `D`-stability of a separable algebra passes
to quotients and hereditary subalgebras.  Since `O_infinity` is strongly
self-absorbing, every hypothetical commutative hereditary shadow `C` would
itself be O-infinity-stable.

That is impossible for a nonzero commutative algebra.  Such an algebra has a
character, while O-infinity-stability implies strong pure infiniteness and
hence absence of characters.  The multiplier-algebra argument gives the same
contradiction directly: a character of `C tensor O_infinity` would restrict
to a character on the unital multiplier copy of `O_infinity`.

The argument is quotient-by-quotient and does not infer shadowlessness merely
from a property of `E` itself.

## Dimension audit

Nuclearity of `A` implies nuclearity of `A tensor O_infinity`.  The reverse
implication is sometimes left implicit but is essential for the infinite
case: the inclusion `a |-> a tensor 1` has the completely positive left
inverse `id_A tensor omega` for any state `omega` on `O_infinity`.  Nuclearity
passes through this completely positive retract.  Hence a nonnuclear `A`
produces a nonnuclear envelope and its nuclear dimension is infinite.

For nuclear `A`, the envelope is separable, nuclear, and O-infinity-stable.
Bosa--Gabe--Sims--White give nuclear dimension at most one.  Dimension zero
would make the envelope AF, which is incompatible with nonzero strong pure
infiniteness, so the value is exactly one.

## Primary sources

* Andrew Toms and Wilhelm Winter, *Strongly self-absorbing C-star algebras*,
  Transactions of the AMS 359 (2007), for permanence of tensorial absorption
  under quotients and hereditary subalgebras;
* Eberhard Kirchberg and Mikael Rordam, *Infinite non-simple C-star algebras:
  absorbing the Cuntz algebra O-infinity*, Advances in Mathematics 167
  (2002), for O-infinity absorption and strong pure infiniteness;
* Joan Bosa, James Gabe, Aidan Sims, and Stuart White, *The nuclear dimension
  of O-infinity-stable C-star algebras*, Advances in Mathematics 401 (2022),
  article 108250, for the one-colour upper bound;
* Wilhelm Winter and Joachim Zacharias, *The nuclear dimension of C-star
  algebras*, Advances in Mathematics 224 (2010), for finite nuclear dimension
  implying nuclearity and nuclear dimension zero characterizing separable AF
  algebras.

## Boundary

This is an exact subclass computation, not a solution of unrestricted
Problem LXXXI.  The absorption hypothesis deliberately removes every type-I
shadow.  It does not address how a one-dimensional continuous-trace layer can
accumulate against a non-type-I layer in an algebra which is not globally
O-infinity-stable.
