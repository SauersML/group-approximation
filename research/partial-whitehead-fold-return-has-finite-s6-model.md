---
rg: 2
id: partial-whitehead-fold-return-has-finite-s6-model
kind: claim
title: The literal partial-Whitehead fold return has a finite marked S6 model
invalidates:
  - partial-whitehead-fold-return-closes-code
artifacts:
  - research/partial-whitehead-fold-return-s6-proof.md
distinct_from:
  intermediate-fold-arm-has-finite-s6-model: that authenticates the propagated arm by an abstract involution W; this factors W into the two actual opposite-root arm occurrences and transports both factors to the reused fold arms.
  one-arm-range-sum-whitehead-has-marked-model: that fixes one Pauli arm through each output Whitehead but does not propagate the fold through a second arm and return it; this includes the intermediate and final return rows.
---

**ESTABLISHED LITERAL-WHITEHEAD FIREWALL.**  Start with the full shared-arm
table

```text
C_0C_1=J,
[C_0,S]=E,             [C_1,S]=1,       [J,S]=E,
[T,E]=M,               [S,T]=1,
W^2=1,                 WSW^(-1)=E,                    (PFR1)
```

from `intermediate-fold-arm-has-finite-s6-model`.  Now require that the
intermediate transporter is not an abstract actor.  Add involutory root
occurrences `U,V` and fixed root-position transports `P,Q` with

```text
W=UVU,                 PUP^(-1)=S,       QVQ^(-1)=T.  (PFR2)
```

Thus `(PFR2)` is the literal characteristic-two partial-Whitehead word: its
first and third factors use the same `s` occurrence, its middle factor uses
the `t` occurrence, and both are tied to the two arms already used in the
fold propagation and final return.  This is an occurrence-sharing condition,
not merely covariance of the output label.

The complete table `(PFR1)--(PFR2)` still has an exact finite marked model.
Inside `S_6`, use the preceding model

```text
S  =(3 4)(5 6),          T=(5 6),
C_0=(1 2)(4 5),          C_1=(3 6)(4 5),
J  =(1 2)(3 6),          E=(3 6)(4 5),
W  =(4 6),               M=(3 4)(5 6),                (PFR3)
```

and additionally put

```text
U=S,              V=(3 5),       P=(1 2),       Q=(3 6).  (PFR4)
```

Every displayed element is an involution.  Direct permutation calculation
gives

```text
UVU=(4 6)=W,       PUP^(-1)=S,       QVQ^(-1)=(5 6)=T. (PFR5)
```

The old rows `(PFR1)` remain exact, and `M=S` is nonidentity.  Hence the
left regular representation of the generated finite subgroup has zero
defect on every row while

```text
||lambda(M)-1||_2=sqrt(2),       ||lambda(M)-1||_op=2. (PFR6)
```

Therefore attaching the actual three-factor opposite-root occurrence to
both shared coefficient arms does not yet give an MF payment.  The surviving
freedom is now sharply located in the two root-position transports: the
finite model can identify the two coefficient-labelled occurrences by
unrelated conjugacies `P,Q`.  A next cell must place those transports in the
prescribed native Weyl/Whitehead mixed squares, or otherwise make the
coefficient action a left/right multiplication action on one matrix corner.
No Property `(T)`, Kazhdan input, stability theorem, trace hypothesis,
literature result, or local compilation is used.

## Attempts

- **Factor the already authenticated `W`.**  This rules out treating `W`
  as a free symbol, but `(PFR4)--(PFR5)` shows that the existing `S_6`
  packet already contains a compatible factorization.
- **Authenticate the final arm as well.**  The middle factor `V` is
  conjugate to the literal final `T` occurrence, yet the mark survives.
  Conjugacy of coefficient-labelled root occurrences is not equality of
  their multiplicity actions.

DERIVATION
partial-whitehead-fold-return-s6-proof

