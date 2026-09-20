---
rg: 2
id: wave2-detector-psl19-second-simple-quotient-proof
kind: route
title: Check three edge identities in projective matrices, then apply the subdirect-product alternative for a simple group
target: wave2-detector-psl19-has-second-simple-quotient
requires:
  - wave2-detector-psl19-perfect-first-kernel
  - hrf-alt-psl2-detectors-need-new-composition-factors
---

All matrices are read projectively modulo19. Direct multiplication gives

```
u^-1 x_12 u = x_12,
v^-1 x_13 v = x_13,
u^-1 x_23 u = v^-1 x_23 v.
```

Thus the three vertex maps agree on each edge and define `f_1` on the
colimit. Both `f_0` and `f_1` are surjective because they are identity
on vertex1. They differ on vertex2: its two edge generators generate
`Q`, and the nonidentity `u` cannot centralize both. Alternatively the
displayed executable certificate directly checks the projective matrices.

The image of `(f_0,f_1)` is a subdirect product of the nonabelian simple
group `Q` with itself. By the elementary Goursat alternative it is
either all of `Q×Q` or the graph of an automorphism of `Q`. Its image
on vertex1 contains the entire diagonal, so the graph alternative
would be the diagonal itself and would force `f_0=f_1` everywhere.
The differing vertex2 maps rule this out. The product map is therefore
surjective, and `f_1(N)=Q`.

The script enumerates `PGL_2(19)` and its centralizers of the first two
edges; each has20 elements. It checks all400 conjugator pairs for the
third edge identity and finds exactly the identity pair and the stated
pair. The theorem only needs the displayed nonidentity pair, so it
does not rely on a classification of all abstract automorphisms of `Q`.

Finally the reviewed PSL2 degree-two vanishing and extension closure
give `H^2(Q×Q;F_5)=0`. Hence this product quotient does not itself
supply a nonzero central lift discrepancy. Its deeper kernel remains
a possible source of new modular layers; this proof does not analyze it.
