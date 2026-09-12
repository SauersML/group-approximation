---
rg: 2
id: binary-jacobson-first-alternating-ts-closure-relation
kind: claim
title: A two-raw-occurrence nested commutator exposes the full-cycle TS closure beyond the Jacobson one-step envelope
artifacts:
  - research/binary-jacobson-first-alternating-ts-closure-proof.md
distinct_from:
  binary-jacobson-one-step-finite-type-envelope-is-marked-mf: that retains every finite-packet relation and every one-step balanced conjugation endpoint; this gives an explicit reduced kernel word which multiplies one S-bearing and one T-bearing occurrence.
  binary-jacobson-first-opposite-polar-package-is-finite: that uses the balanced actor and one opposite root and obtains only a finite dihedral package; this relation simultaneously consumes the complete constant three-cycle and the identity TS=1.
  binary-jacobson-tail-phase-cannot-correct-closing-fold: that computes the degree switch created by the closing fold; this identifies an explicit full-cycle coefficient relation whose intermediate T-root can act on its raw range.
  binary-jacobson-first-mixed-kernel-is-three-syllable: that proves the optimal balanced-syllable length is three and gives the controlled-swap relator; this longer nested commutator is not a length optimum, but uniquely exposes the root x_21(T) whose compression can be tested on the literal folded source.
---

**ESTABLISHED.**  In the notation of
`binary-jacobson-one-step-finite-type-envelope-is-marked-mf`, put

```text
b=x_12(1),             z=x_23(1),             k=x_31(1),
q=x_13(Q),             A=x_13(1)=[b,z],
c=qA=x_13(ST),         s=h z h,                t=h c h.  (JAR1)
```

Then the literal Jacobson matrices give

```text
s=x_13(S),             t=x_23(T),
u:=[t,k]=x_21(T),      [u,s]=x_23(TS)=z.                (JAR2)
```

Equivalently the fixed word

```text
W=[[h c h,k],h z h] z                                  (JAR3)
```

is trivial in `E=EL_3(J)`.  It uses exactly two distinct raw coefficient
occurrences, one carrying `T` and one carrying `S`, and the full constant
cycle: `b,z` form `A=[b,z]`, while `k` turns the T-root into the compatible
root `x_21(T)`.  The last commutator is precisely where `TS=1` is consumed.

On the other hand, `W` is nontrivial in the virtually free envelope

```text
Gamma_F=F *_K (K semidirect C_2)
```

of the prerequisite.  Hence

```text
1 != W in ker(Gamma_F -> E).                             (JAR4)
```

This is an explicit alternating relation beyond the complete one-step type
graph which simultaneously exposes both one-sided coefficients and all
three constant-cycle edges.  It is **not** shortest in balanced-syllable
length: `binary-jacobson-first-mixed-kernel-is-three-syllable` gives the
optimal three-syllable controlled-swap relation.  The point of `(JAR3)` is
instead that its intermediate word is the literal coefficient root
`x_21(T)`, so its compression can act on the folded `SQ` source.  Relations
involving only one raw conjugate cannot perform this `TS` multiplication.

The relation also exposes the natural next polar candidate.  On any common
reducing cut for the literal roots involved, compression of `u=x_21(T)`
commutes with `z,x_14(Q),x_43(1)` and satisfies

```text
u s u=z s,
[u,x_14(SQ)]=x_24(Q),
[u,x_14(Q)]=1.                                          (JAR5)
```

Thus it genuinely distinguishes the folded raw coefficient `SQ` from the
literal target coefficient `Q`.  What is not proved here is that the polar
of its compression to the selected raw range has full source and range, or
that it supplies all four common intertwining rows.  Those are the remaining
finite-coordinate assertions, rather than the identification of a kernel
relation.

DERIVATION
binary-jacobson-first-alternating-ts-closure-proof
