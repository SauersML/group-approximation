---
rg: 2
id: titz-witzel-soficity-is-one-finite-csp
kind: claim
title: Soficity of the smallest Titz--Witzel kernel is one explicit three-permutation finite CSP
distinct_from:
  titz-witzel-mapping-tori-are-virtually-products: That classifies cyclic automorphism extensions and computes their MF radicals; this isolates the only remaining property, soficity, directly in the smallest geometric presentation.
  titz-witzel-simple-kazhdan-cat0-lattices-exist: That imports the group and its presentation; this converts its soficity into a one-word sequence of finite permutation feasibility problems and excludes the apparent closure shortcuts.
artifacts:
  - research/artifacts/titz-witzel-sofic-structure-audit-2026-08-26.md
---

**OPEN FINITE GATE.**  Let `barGamma=barGamma_1^2` be the 15-generator,
24-relator group of Titz Mite--Witzel Proposition 4.3, and put

```text
w=(g1 g6^(-1))^4=(g1 g3)^4.                            (TWS1)
```

Its index-two subgroup `K=Gamma_1^2` is infinite, simple, torsion-free and
Kazhdan; `w` lies nontrivially in `K` and normally generates `K`.  Then the
following are equivalent:

1. `K` is sofic;
2. `barGamma` is sofic;
3. there are dimensions `d_n` and triples
   `(x_n,y_n,z_n) in Sym(d_n)^3` for which the twelve words in `(TWS4)`
   have normalized Hamming defect tending to zero while

   ```text
   limsup_n d_H(y_n^8,1)>0.                             (TWS2)
   ```

Thus a positive solution to this one finite CSP, together with
`simple-kazhdan-groups-have-full-mf-radical`, makes
`K x Z` the requested finitely presented torsion-free sofic group with exact
Kazhdan MF radical `K` and quotient `Z`.

The presentation reduces much further before a computation.  Put
`x=g3`, `y=g7`, `z=g12`, and abbreviate the following words in `x,y,z`:

```text
A=x y^(-2),                 B=z y^(-1) z,
C=y^2 x,                    D=z y^(-1) z x y^(-1),
E=y^(-1) z^2,               F=x^(-1) z^2 y^(-1) x,
S=z^(-1) x^(-1) y z^(-2),  H=z^2 y^(-1).              (TWS3)
```

Then elementary Tietze elimination gives the three-generator presentation

```text
<x,y,z | A^2,B^2,C^2,E^2,F^2,S^2,H^2,
         A C D B, x z C S, A E D F, D F E H, D S F E>. (TWS4)
```

Indeed the eliminated generators are

```text
g1=A, g2=B, g3=x, g4=C, g5=D, g6=x^(-1), g7=y,
g8=D^(-1), g9=y^(-1), g10=E, g11=F, g12=z,
g13=S, g14=z^(-1), g15=H.                              (TWS5)
```

Substitution and free cancellation make eight of the thirteen quartics
identities; the other five are exactly the last five words in `(TWS4)`.
The seven length-two constraints become the seven square relations there.
The marked word is `(A x)^4=(x y^(-2)x)^4`; the relation `A^2=1` and the
identity `A y^2=x` give `A x=y^2`, so the mark is exactly `y^8` in the
presented group.  Quantitatively,
`d_H(Ax,y^2) <= d_H(A^2,1)`, hence the two separation objectives are
equivalent along approximate solutions.  The terminal finite gate therefore
has only three permutation variables, twelve relator equations, and the
objective `limsup d_H(y^8,1)>0`.

No standard sofic permanence theorem closes `(TWS2)`.  Property `(T)` gives
Serre's property `FA`, so every reduced graph-of-groups decomposition is
trivial.  The product-of-trees lattice occurs as a subgroup of `K`, not as a
sofic overgroup.  Conversely, `K` cannot embed in a group acting properly on
a product of trees: such a group has the Haagerup property, inherited by
subgroups, while an infinite property-`(T)` group cannot have the Haagerup
property.  The exotic-building action itself gives biautomaticity and a word
problem, not finite permutation approximations.

There is also a sharp obstruction to the most literal graph-cover attack.
Titz Mite--Witzel prove that the Cayley graph for the displayed generators
has no perfect finite `r`-local model for any `r>=5`: rigidity of radius-four
balls canonically reconstructs the labels, after which a perfect radius-five
model is a genuine finite action and hence factors through the quotient
`C2`.  Thus finite covers, exact finite building quotients, and perfect random
lifts cannot solve the gate.  This does not prove nonsoficity, because a sofic
model may have a vanishing but nonempty set of defective vertices.  Any
positive construction must exploit precisely such sparse defects.
