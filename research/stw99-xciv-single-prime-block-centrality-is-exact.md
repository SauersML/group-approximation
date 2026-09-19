---
rg: 2
id: stw99-xciv-single-prime-block-centrality-is-exact
kind: claim
title: One fixed prime dimension-drop block exactly tests separable Jiang--Su stability
distinct_from:
  stw99-xciv-separable-zstability-iff-local-prime-dimension-drops: that criterion requests local norm-central copies of every block I_(k,k+1); this theorem proves that the single fixed block I_(2,3) already suffices.
  stw99-xciv-separable-zstability-iff-local-norm-central-z: that criterion requests a local copy of the whole Jiang--Su algebra; this theorem uses only one finitely generated nonsimple subhomogeneous algebra.
  stw99-xciv-two-norm-centrality-does-not-control-norm-centrality: that obstruction concerns tracially central representatives; every diagonal commutator in this theorem converges in operator norm and therefore defines a map into the norm sequence relative commutant.
  stw99-xciv-norm-matrix-tower-has-zstable-hull: that sufficient theorem assumes coherent finite-dimensional norm approximation and growing Bratteli multiplicities; this is an equivalence for arbitrary unital ambient algebras and assumes no approximation tower.
artifacts:
  - research/artifacts/stw99-xciv-single-block-diagonal-audit-2026-08-30.md
---

Fix the prime dimension-drop algebra

```text
D=I_(2,3)
 ={f in C([0,1],M_2 tensor M_3):
    f(0) in M_2 tensor 1, f(1) in 1 tensor M_3},
```

and a finite self-adjoint contractive generating set `H` for `D`.  For every
unital C*-algebra `B`, the following are equivalent:

1. every norm-separable subset of `B` is contained in a separable unital
   `Z`-stable C*-subalgebra of `B`;
2. for every finite `F subset B` and every `epsilon>0`, there is a unital
   homomorphism `psi:D->B` such that

   ```text
   ||[a,psi(h)]||<epsilon              (a in F, h in H). (1)
   ```

Consequently STW Problem XCIV is equivalent to local operator-norm
centralization in `R` of the **single fixed block** `I_(2,3)`.  A negative
answer has a finite certificate consisting of a finite `F subset R` and a
`delta>0` such that every unital `psi:I_(2,3)->R` satisfies

```text
max_(a in F,h in H)||[a,psi(h)]||>=delta.               (2)
```

No family of increasing dimension-drop sizes is required.  The result makes
no assertion that `R` satisfies `(1)`.
