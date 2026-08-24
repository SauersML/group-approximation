---
rg: 2
id: finitely-presented-grushko-towers-with-prescribed-mf-reflection
kind: claim
title: Every finitely presented MF group has infinitely many finitely presented Grushko thickenings with the same MF reflection
artifacts:
  - research/fp-grushko-mf-reflection-towers-proof.md
---

Let `B` be the nontrivial finitely presented Kazhdan Hilbert-hotel group with
full MF radical and one normally generating compression defect.  For `n>=1`
put

```text
A_n=B * ... * B                 (n free factors).
```

Then:

1. `A_n` is finitely presented, perfect, and has full MF radical;
2. every homomorphism from `A_n` to a compact group or to `GL_m(k)` for any
   field `k` is trivial;
3. every nontrivial quotient of `A_n` again has full MF radical;
4. the groups `A_n` are pairwise nonisomorphic; their Grushko decomposition
   has exactly `n` nontrivial freely indecomposable factors;
5. `A_1` has property `(T)` and one end, while every `A_n` for `n>=2` acts
   nontrivially on its Bass--Serre tree and has infinitely many ends.

For every finitely presented MF group `Q`, define

```text
E_(n,Q)=A_n x Q.
```

Then the `E_(n,Q)` are pairwise nonisomorphic finitely presented non-MF
groups and

```text
Rad_MF(E_(n,Q))=A_n x {1},
R_MF(E_(n,Q))=Q,                                      (GT1)
Hom(E_(n,Q),M) ~= Hom(Q,M)                            (GT2)
```

naturally for every MF target `M`.  The same factorization holds for compact
targets and all finite-dimensional linear targets over every field.

Thus one prescribed finitely presented MF group is the complete MF-visible,
compact-visible, and finite-dimensional-linear-visible quotient of infinitely
many pairwise nonisomorphic finitely presented groups.  Their invisible
kernels are distinguished internally by free-product length and externally
by their end structure.
