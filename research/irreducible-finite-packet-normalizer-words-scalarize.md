---
rg: 2
id: irreducible-finite-packet-normalizer-words-scalarize
kind: claim
title: Ordinary words in one irreducible finite-packet normalizer reduce to scalar multiplicity relations
distinct_from:
  projective-label-pullbacks-have-conjugate-stationary-absorbers: that gives an explicit escape for locally trivial label words; this classifies arbitrary ordinary normalizer relations.
  fixed-extraspecial-packet-is-morita-neutral-for-code-rounding: that treats centralizing occurrences only; this includes every automorphism-normalizing occurrence and every multi-occurrence word.
---

# Ordinary words in one irreducible finite-packet normalizer reduce to scalar multiplicity relations

ESTABLISHED. Let a finite packet algebra act irreducibly on `V`, and amplify
it to `V tensor M`. Every unitary `U` normalizing the packet has a unique
factorization up to scalar

```text
U=C_alpha tensor Q,                                      (NS1)
```

where `alpha` is the induced packet automorphism, `C_alpha` is one fixed
intertwiner on `V`, and `Q in U(M)`. This is Schur's lemma applied after
removing `C_alpha`.

Accordingly every ordinary group word in packet constants and normalizing
occurrences factors as

```text
W(U_1,...,U_n;packet)=A_W tensor W_Q.                    (NS2)
```

If the exact relation `W=I` is satisfiable, `(NS2)` forces `A_W` to be scalar:
a simple tensor `A tensor B` can equal the identity only when both factors
are reciprocal scalars. The relation on the multiplicity algebra is therefore
only

```text
W_Q=lambda_W^{-1} I.                                    (NS3)
```

This applies to words coupling arbitrarily many occurrences. Hence no
ordinary multi-occurrence group relation among normalizers of one fixed
irreducible packet can directly impose a non-scalar constraint on the
multiplicity algebra. The packet contributes only finitely many scalar
cocycle/affine phases. If those scalar equations themselves have a robust
non-matricial obstruction, that is precisely a projective/LCS obstruction on
the multiplicity variables, not rigidity supplied by the finite packet.

The minimal relation evading the homogeneous conjugate absorber is one with
`A_W=lambda I`, `lambda != 1`; it creates the affine phase `(NS3)`. To evade
the full scalarization theorem while retaining an exact marked model, a
construction must leave at least one hypothesis: use occurrences that do not
normalize one common irreducible packet, move between inequivalent packet
sectors/corners, or impose a compression/projection relation not expressible
as an ordinary unitary group word. Merely increasing the arity of a normalizer
word does not help.

