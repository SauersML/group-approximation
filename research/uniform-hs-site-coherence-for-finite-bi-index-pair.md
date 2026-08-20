---
rg: 2
id: uniform-hs-site-coherence-for-finite-bi-index-pair
kind: claim
title: A finite-bi-index subgroup pair has dimension-independent Hilbert--Schmidt site coherence
distinct_from:
  matrix-recovery-of-schur-flip-wreath-sites: that recovers a microstate-dependent finite supercritical set of wreath sites; this asks for one coherent infinite coset-indexed family, after a uniform correction of the acting group and stabilizer commutant.
  coherent-configuration-orbital-rounding: that seeks an integral orbital basis from near-normal characters; this asks only to make conjugates of one lamp independent of their coset representatives in normalized HS norm.
---

Find a finitely presented group `L` and a finitely generated infinite-index
subgroup `H` with finite `H\L/H`, together with universal constants
`C,delta_0>0`, such that the following rounding holds for `(FCT1)`.

For every finite-dimensional tuple with relator defect below `delta_0` and
with a positive-density spectral carrier on which `J` is near `-I`, either a
fixed amount of normalized-HS energy is already paid, or on a subcarrier
losing at most `C E_rel` mass there are

1. an exact representation `sigma` of `L`;
2. an involution `A` commuting with `sigma(H)`; and
3. closeness on the finitely many base lamp and pair-orbit relations,

all with squared error at most `C E_rel`.  Consequently

```text
A_(gH)=sigma(g) A sigma(g)^*
```

is independent of the representative and the conjugates of the finitely many
pair relators give

```text
||A_x A_y + A_y A_x||_2 <= C sqrt(E_rel)       for every x!=y,   (FSC1)
```

with the same constant for the entire infinite coset space.

## Attempts

- Raw word representatives fail: comparing two representatives of one coset
  accumulates relator error with an unbounded stabilizer word.
- Finite pair-orbit type controls the number of defining relations but does
  not itself round the acting tuple or the stabilizer commutant.
- A plausible sufficient package is same-dimension HS stability of `L` plus
  an adjoint spectral gap for `H`.  This implication is now proved by
  `hs-stable-kazhdan-finite-bi-index-pair-gives-site-coherence`; the remaining
  structural search is `hs-stable-finite-bi-index-kazhdan-pair-exists`.
- Flexible stabilization must also preserve a positive fraction of the
  marked `J=-1` carrier; arbitrary dimension padding would reintroduce the
  dilution being attacked.
