---
rg: 2
id: atlas-q14-simple-overgroup-reduction-proof
kind: route
title: Pass to a maximal normal quotient and use the classical A8 alignment exclusion
target: atlas-q14-finite-quotient-is-simple-overgroup-test
requires:
  - atlas-a4-finite-quotient-escape-fence
  - atlas-a4-packet-biclique-decomposition
  - atlas-a4-19243-classical-collapse
  - atlas-q14-adds-stratified-thirteenth-double-coset
---

Suppose first that `phi:Gamma_+ -> F` is a nontrivial finite quotient, with
`F` replaced by the image.  Choose a maximal proper normal subgroup `N` of
`F` and put `S=F/N`.  The composite map

```text
Gamma_+ ->> S                                        (SPR1)
```

is again a nontrivial finite quotient.  Since every defining relation of the
packet-plus-`19243` quotient also holds in `Gamma_+`, the established finite
quotient chart dichotomy applies directly to `(SPR1)`: both restrictions to
the two `A8` factors are injective.  In particular `S` contains `A8`, so it
is nonabelian; maximality of `N` makes it simple.  Surjectivity of `(SPR1)`
says that the two chart images generate `S`.

The thirty listed packet occurrences impose only the twelve distinct
pair-cube constraints in the simple pair graph

```text
K_(2,2) disjointUnion K_(2,4).
```

The collision word remains `q_19243=1`.  Finally, the two letters in `q_14`
are involutions, so

```text
(i_1(t23)i_2(t23))^2=1
 iff i_1(t23)i_2(t23)=i_2(t23)i_1(t23)
 iff [i_1(t23),i_2(t23)]=1.                         (SPR2)
```

This proves necessity of the marked system.

The group `S` cannot be isomorphic to `A8`.  If it were, injectivity of both
chart maps would make both surjective, and their relative identification
would be an automorphism of `A8`.  The complete inner/outer automorphism
audit says that no automorphism alignment satisfies the packet together with
`q_19243`, even before q14 is imposed.  Hence `S` is strictly larger.

Conversely, maps `(SOT2)` satisfying the marked system make every defining
relator of `Gamma_+` vanish: the twelve edge relations are exactly the
distinct relations represented by the thirty packet occurrences, the
collision is imposed, and `(SPR2)` is q14.  The universal property gives a
homomorphism `Gamma_+ -> S`; the generation hypothesis makes it surjective.
Since either embedded `A8` is nontrivial, this is a nontrivial finite quotient.
This proves sufficiency and the equivalence.
