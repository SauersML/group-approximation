---
rg: 2
id: torsion-normal-generator-mf-character-criterion
kind: claim
title: A torsion normal generator has full MF radical exactly when all MF characters are trivial
artifacts:
  - research/torsion-normal-generator-mf-character-criterion-proof.md
distinct_from:
  simple-torsion-non-mf-iff-trivial-mf-characters: that uses simplicity to obtain pointwise Hilbert--Schmidt separation of every nonidentity element; this only needs a finite-order normal generator and detects nontriviality at that mark.
  torsion-normal-generator-has-full-support-corona-core: that reblocks one surviving corona image to make the marked spectral support macroscopic; this takes a trace limit and packages the exact character criterion.
---

Call `chi:G->C` an **MF character** when it is a pointwise limit of normalized
traces of operator-norm asymptotic unitary representations.  Let `G` be a
finitely generated group and let `a in G` be a nonidentity finite-order
element which normally generates `G`.  Then

```text
Rad_MF(G)=G
  iff
every MF character of G is the trivial character 1.                 (TMF1)
```

Only the forward implication is formal.  For the reverse implication, any
nontrivial corona homomorphism must keep `a` nontrivial because `a` normally
generates `G`.  Active-core reblocking gives an operator-norm asymptotic
model in which `a` stays a fixed positive normalized Hilbert--Schmidt
distance from the identity.  A trace-convergent subsequence therefore gives
a nontrivial MF character.

No simplicity, Property `(T)`, stability theorem, or literature input is
used.

DERIVATION
torsion-normal-generator-mf-character-criterion-proof
