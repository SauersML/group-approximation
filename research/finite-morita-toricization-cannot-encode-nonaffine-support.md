---
rg: 2
id: finite-morita-toricization-cannot-encode-nonaffine-support
kind: claim
title: Finite Morita group corners cannot functorially encode a nonaffine BCS answer support
distinct_from:
  finite-group-selector-induction-barrier: that says every compatible selector character occurs somewhere in the marked representation category; this combines it with center preservation to rule out finite Morita answer-algebra compilation
  central-word-state-face-compiler: that is the surviving nonfunctorial state-face target; this proves why a finite representation-functorial Morita implementation cannot supply it
---

ESTABLISHED.  Let

```text
R <= {+1,-1}^m
```

be a nonempty BCS answer support, with answer algebra `C^R` and coordinate
functions `f_i(r)=r_i`.  Let `F` be a finite group with a central involution
`J` and commuting involutions `z_1,...,z_m`.  Put

```text
p_-=(1-J)/2 in C*(F).
```

Consider the strongest finite-Morita version of a local toric compiler:

1. a full corner of a matrix amplification of `p_- C*(F)` is strongly
   Morita equivalent to `C^R`; and
2. under the induced isomorphism of centers, the coordinate function `f_i`
   is represented by the marked group element `p_- z_i`.

> **Theorem.**  Such a compiler exists only when `R` is affine over `F_2`.
> In particular it cannot encode a genuinely nonlinear BCS predicate.

## Proof

Strong Morita equivalence preserves centers and the primitive-ideal/simple-
module space.  Matrix amplification and passage to a full corner do not
change either.  Since every `f_i` is central in `C^R`, condition 2 forces

```text
p_- z_i in Z(p_- C*(F)).                                (FMT1)
```

Consequently each `z_i` acts as a scalar on every irreducible representation
of `F` on which `J=-1`.  The joint scalar pattern of the `z_i` labels that
simple block.  Because the coordinate functions separate the points of `R`
and the Morita center map is an isomorphism, the set of these scalar patterns
is exactly `R`.

Now put

```text
A=<J,z_1,...,z_m> <= F.
```

For every character `chi` of `A` with `chi(J)=-1`, the finite-dimensional
representation

```text
Ind_A^F(chi)                                             (FMT2)
```

is nonzero and lies entirely in the `J=-1` sector.  Some irreducible marked
summand contains the inducing character on restriction to `A`.  By `(FMT1)`
the `z_i` are scalar on that whole summand, so its scalar pattern is precisely

```text
(chi(z_1),...,chi(z_m)).                                 (FMT3)
```

Thus every compatible character of `A` occurs among the patterns in `R`.
Conversely every marked scalar pattern is such a character.  The restriction
of the affine character slice

```text
{chi in A-hat: chi(J)=-1}
```

to the `z_i` coordinates is affine.  Hence `R` is affine.  End proof.

## Why a controlled phase in one matrix block does not contradict this

Inside `M_2(C^R)` one may define the exact reversible controlled flip

```text
C_f(r)=X^(f(r))
```

for an arbitrary Boolean predicate `f`.  Conjugating an ancilla `Z` by
`C_f` and uncomputing gives the phase `(-1)^(f(r))`.  All of these matrices
have finite order, and on the intended finite block they generate a finite
group.  Thus **local nonlinear reversible computation is not the problem**.

The problem is functoriality across representations.  In the intended block
the visible coordinate algebra is a noncentral MASA.  It is not the center of
the marked group corner, so it is not transported by Morita equivalence to
every representation.  Other marked irreducibles supplied by `(FMT2)` carry
the forbidden selector characters.  Matrix amplification only changes their
multiplicity.

Therefore a finite ancilla has exactly two options:

1. put the answer coordinates in the Morita center, in which case the theorem
   forces affine/LCS support; or
2. put them in a selected noncentral MASA, in which case a separate global
   state/type-selection theorem is required to exclude the other marked
   representations.

The second option is not ruled out.  But for the fixed tracial non-`R^U` BCS,
proving that **the whole target clause face** occupies the selected MASA and
that every finite-dimensional target state decodes back to the BCS is exactly
`central-word-state-face-compiler`.  By
`phase-safe-toric-gap-implies-nonhyperlinear`, completing that selection would
already produce the desired finitely presented nonhyperlinear group.  Finite
Morita theory alone does not lower that final gate.

## Attempts

The controlled-flip construction above is the strongest obvious attempt to
evade the theorem.  It succeeds inside one chosen matrix block and fails
exactly because its selector algebra is a noncentral MASA: induction supplies
other marked blocks, while finite Morita equivalence has no mechanism for
forcing the state into the chosen one.  The surviving attack is therefore the
nonfunctorial state-face compiler recorded in `central-word-state-face-compiler`.
