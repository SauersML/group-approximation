---
rg: 2
id: orbitwise-scalar-relators-give-quotient-representation
kind: claim
title: Orbitwise scalar relators produce a genuine representation of the normal quotient
distinct_from:
  scalar-relator-compression-does-not-kill-normal-ideal: that proves scalar relations on one compressed fibre are insufficient; this supplies the exact positive repair by imposing those relations on every translate of the fibre.
  zpc-readable-control-freezing-to-lcs: that is the game-specific existence of a frozen LCS solution; this is an unconditional operator-algebra lemma once an orbitwise coherent fibre has been found.
---

Let `F=F(S)` act unitarily by `pi` on `H`, let `J` be a central involution,
and let `P` be a nonzero projection with

```text
P pi(J)=pi(J)P=-P.                                      (ORQ1)
```

Fix finitely many relator words `r_j` and signs `lambda_j in {+1,-1}`.
Suppose that for every `g in F` and every `j`,

```text
P pi(g^-1 r_j g) P=lambda_j P.                          (ORQ2)
```

Then the quotient group

```text
Q=<S,J | J central, J^2=1, r_j=lambda_j for every j>   (ORQ3)
```

has a nonzero unitary representation in which `J=-I`.  In particular `J` is
nontrivial in `Q`.

No generator need preserve `P H`.  The representation is obtained on the
cyclic orbit hull

```text
K=closure(span{pi(g)xi:g in F, xi in P H}).             (ORQ4)
```

Thus orbitwise constancy of the selected **relation menu**, rather than
invariance of every readable bit, is sufficient for readable-control
freezing.
