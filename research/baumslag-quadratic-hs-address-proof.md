---
rg: 2
id: baumslag-quadratic-hs-address-proof
kind: route
title: Conjugate every lamp commutator to a short null word and apply the quadratic Dehn bound
target: baumslag-torsion-host-is-a-quadratic-hs-address-register
requires:
  - hs-dehn-modulus-bounded-by-dehn-function
---

Cornulier--Tessera identify `(BQA1)` with their group `Lambda_p` at `p=2`,
prove that it contains `(Z/2Z) wr Z`, and prove that its Dehn function is
quadratic.  Kassabov--Riley give the same lamplighter subgroup description:
the conjugates of `a` by powers of the shift commute and are independent.

For `k=j-i`, conjugation by `b^i` identifies `[B_i,B_j]` with the conjugate
of

```text
[a,b^k a b^(-k)],
```

whose word length is at most `4|k|+4`.  Conjugating a null word does not
increase its van Kampen area, so the quadratic Dehn estimate gives `(BQA3)`.
The standard normalized-HS van Kampen telescope bounds evaluation of a null
word by its area times the largest defining-relator defect.  Since each such
defect is at most `sqrt(E(rho))`, `(BQA4)` follows from
`hs-dehn-modulus-bounded-by-dehn-function`.

Finally, the direct-product model with an arbitrary payload representation
shows the stated boundary: address relations alone impose no conditional
dependence on payload spectral projections.

