---
rg: 2
id: leavitt-corners-cannot-compress-external-variable-proof
kind: route
title: Separate internal matrix entry decoding from equations over arbitrary group extensions
target: leavitt-corners-cannot-compress-external-variable
requires:
  - leavitt-omega-has-an-explicit-distorted-target
  - leavitt-hidden-face-three-gate-retractions
---

## What orthogonal packing really proves

Let `R` be the binary Leavitt algebra.  If `c,d in R` and `(i,j)!=(k,l)` are
matrix positions with no cross term, then

```text
x_ij(c)x_kl(d)=1                                      (OC1)
```

forces `c=d=0`: compare the two off-diagonal matrix entries.  The same fact
can be expressed with orthogonal prefix idempotents.  This is a valid
system-to-one-equation lemma **for errors already known to lie in those root
subgroups of `EL_n(R)`**.

## Why the KL transport errors do not have that type

The desired errors are

```text
E_a=z^(-1)a_1z A_0^(-1),
E_r=z^(-1)r_1z B_0^(-1),                              (OC2)
```

where `z` is the stable letter in an arbitrary overgroup of the coefficient
group.  Neither error in `(OC2)` is a matrix over `R` before the transport
relation has already been proved.  Consequently it has no matrix entry to
which `(OC1)` can be applied.

The self-similar corner operation

```text
g |-> s_i g t_i + (1-s_i t_i)                         (OC3)
```

is defined for ring elements.  It uses addition and the nonunits `s_i,t_i`;
there is no group word in fixed coefficient units which evaluates `(OC3)` on
an arbitrary external element `z`.  Similarly, conjugating `z` by fixed
Leavitt units only gives another arbitrary overgroup element.  It does not
make `z` preserve the chosen idempotents or root supports.

Thus a product of two allegedly orthogonal expressions involving `(OC2)` is
only one group relator.  Matrix-entry comparison would silently assume that
the unknown already lies in the Leavitt matrix group, while the KL problem
quantifies over all group extensions.  This is a type error, not a missing
Steinberg calculation.

## Higher degree does not assign independent jobs to the lifts

For an equation of exponent sum `m`, every relator in the index-`m`
Reidemeister--Schreier rewrite has stable-letter exponent `+1`; the relators
form one orbit under conjugation by the original variable.  Raising the
degree to three does provide three relators and hence two constraints after a
formal elimination, but their coefficient traces are cyclic copy shifts of
the same word.  In particular, after setting the stable letter to `1`, if one
lift is the source identity `Omega(a,r)`, then all three lifts are copies of
that same identity.  They cannot literally become a tag equation, an
`a -> A` transport, and an `r -> B` transport, because a copy shift changes
copy indices but not coefficient labels.

This does not prove that every degree-three gadget fails: extra coefficient
faces could interact nontrivially before the stable letter is specialized.
It does rule out the direct three-job reverse engineering and the proposed
orthogonal-support proof.  The remaining route is a group-theoretic test word
whose relative normal form forces both equations in `(OC2)`, or an explicit
multi-cell picture showing the same consequence.
