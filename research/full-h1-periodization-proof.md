---
rg: 2
id: full-h1-periodization-proof
kind: route
title: Use one characteristic free pro-p quotient for every branch
target: full-h1-rank-free-endomorphism-families-periodize
requires: []
---

Choose a prime `p` avoiding all determinants on integral abelianization and
embed `F_n` in its free pro-`p` completion `P`.  Each endomorphism extends
continuously to `P` and acts invertibly on

```text
P/Frat(P)=H_1(F_n;F_p).
```

The pro-`p` Burnside basis theorem makes the extension surjective; Hopficity
of finitely generated pro-`p` groups makes it an automorphism.

Choose an open normal subgroup `U` not containing `y` and intersect all open
subgroups of index at most `[P:U]`.  There are finitely many, so their
intersection `C` is open; automorphisms permute them, so `C` is
characteristic.  Also `C<=U`, hence `Q=P/C` is a finite `p`-group detecting
`y`.  Density makes `F_n->Q` surjective, and every original endomorphism
induces an automorphism `alpha_i` of this same quotient.  Mapping the stable
letters into the finite subgroup `<alpha_1,...,alpha_r><=Aut(Q)` gives the
claimed finite marked quotient of the multiple ascending presentation.
