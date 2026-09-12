---
rg: 2
id: scalar-lcs-character-forbids-a-bcs-section-proof
kind: route
title: Compose a proposed section with the scalar LCS character
target: nonce-bcs-canonical-lcs-cover-has-no-unital-section
requires:
  - every-bcs-is-a-trace-pullback-quotient-of-an-lcs
  - mipstar-bcs-tracial-nonru-exists
---

The LCS cover has the one-dimensional perfect representation

```text
epsilon:A_(L_*)->C,
J |-> -1,
s_x |-> 1,
a_(x,y) |-> 1.                                         (SLS1)
```

This is a unital star-homomorphism because every added row is the
parity-zero identity `x+y+a_(x,y)=0`.

Suppose that a unital star-homomorphism

```text
i:A_(B_*)->A_(L_*)                                      (SLS2)
```

existed. Then

```text
epsilon after i:A_(B_*)->C                              (SLS3)
```

would be a unital star-homomorphism. Composing (SLS3) with the scalar
inclusion `C->R^U` would make `B_*` `R^U)-satisfiable, contradicting
the defining property of the MIP-star source. Hence (SLS2) does not exist.

In particular there cannot be a section `i` with `q after i=id`.
Projectivity of `A_(B_*)` in the unital C-star category would lift its
identity map through the explicit unital surjection

```text
q:A_(L_*)->A_(B_*).
```

The resulting lift would be such a section, so `A_(B_*)` is not
projective.

No assertion that the source has or lacks LLP, local reflexivity, or MF is
needed. The point is categorical: those properties do not imply a
multiplicative section of this quotient. Any local lifting argument must
retain the distinction between a ucp operator-system lift and a unital
star-homomorphism; the latter is ruled out by (SLS1)-(SLS3).
