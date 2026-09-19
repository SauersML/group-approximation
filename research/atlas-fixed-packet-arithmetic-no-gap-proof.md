---
rg: 2
id: atlas-fixed-packet-arithmetic-no-gap-proof
kind: route
title: Projectivize the multiplicity semigroup and kill finite residues by amplification
target: atlas-fixed-packet-arithmetic-has-no-hs-gap
requires:
  - atlas-a4-context-types-live-in-fixed-rational-polytope
  - fixed-depth-rank-mesh-has-zero-hs-density
---

For `(APA1)`, write all congruences as one homomorphism `phi:L->F`, where
`L` is the integral packet-flow lattice and `F` is finite.  If `rF=0`, then
`phi(rx)=r phi(x)=0`.  The representation with multiplicity vector `rx` is
the `r`-fold direct-sum amplification of the representation with vector `x`,
and normalization cancels `r`.  This proves exact residue blindness.

For `(APA2)`, every nonzero `x=sum_j n_jv_j` satisfies

```text
x/d(x)=sum_j alpha_j v_j/d(v_j),
alpha_j=n_j d(v_j)/(sum_l n_l d(v_l)).                 (APA5)
```

The coefficients are nonnegative and sum to one, proving one inclusion.  For
the reverse inclusion, given simplex weights `alpha_j`, choose

```text
n_j(N)=floor(N alpha_j/d(v_j)).
```

After omitting zero target weights and taking `N` large, the coefficients in
`(APA5)` converge to `alpha_j`.  Thus every convex combination is a limit of
normalized integral profiles.  Gordan's lemma supplies finitely many integral
generators for the intersection of a rational polyhedral cone with its
lattice, proving the stated cone version.

The established A4 polytope theorem identifies these normalized integral
flows with exact matrix packet representations and the real points with
tracial multiplicity profiles.  Continuity now proves the gap dichotomy.  A
strict test based only on a nonzero integral numerator has mesh `O(1/d)`, in
agreement with the second required claim.

Finally, finite-group isotypic decomposition gives

```text
End_H(V)=directSum_i I_(S_i) tensor M_(m_i),
```

so its dimension is `sum_i m_i^2`, proving `(APA3)` and `(APA4)`.  This
quadratic statistic identifies a minimal-degree amplification-invariant nonlinear
boundary but also shows directly that it extends continuously to the real
profile simplex.
