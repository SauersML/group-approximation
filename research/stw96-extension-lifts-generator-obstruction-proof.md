---
rg: 2
id: stw96-extension-lifts-generator-obstruction-proof
kind: route
title: Push a hypothetical generator to the quotient and use extension permanence
target: stw96-extension-lifts-generator-obstruction
requires: []
---

Let `F={f_1,...,f_m}` be the finite obstruction in `Q`, and choose
`e_j in E` with `q(e_j)=f_j`.  If all the `e_j` belonged to `C*(g)` for one
`g in E`, then

```text
F subset q(C*(g)) = C*(q(g)).
```

This contradicts the defining property of `F`.  Notice that the argument
preserves the stronger finite-set obstruction, rather than only proving that
`E` is not singly generated.

For nowhere scatteredness, use Hannes Thiel and Eduard Vilalta,
[*Nowhere scattered C*-algebras*, Proposition
4.2](https://doi.org/10.4171/JNCG/526): if `I` is an ideal of `E`, then `E`
is nowhere scattered if and only if both `I` and `E/I` are nowhere scattered.
Here `E/I` is `Q`, so the stated hypotheses give the conclusion.

The single-generation implication uses only functoriality of generated
subalgebras under a surjective *-homomorphism.  The only imported structural
input is Thiel--Vilalta's extension permanence for nowhere scatteredness.
