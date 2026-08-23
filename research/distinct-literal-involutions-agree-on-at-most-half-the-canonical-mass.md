---
rg: 2
id: distinct-literal-involutions-agree-on-at-most-half-the-canonical-mass
kind: claim
title: Distinct literal group involutions agree on at most half of the canonical mass
distinct_from:
  finite-support-one-sided-stabilizers-are-torsion: that shows exact agreement on a nonzero finite-support mask forces torsion; this computes the sharp canonical trace ceiling of every such mask.
  high-plancherel-irrep-has-nearly-uniform-fixed-abelian-spectrum: that controls the joint sign spectrum of a fixed elementary abelian subgroup inside one high-mass irreducible; this treats one agreement row in the canonical regular trace of an arbitrary group.
  rowwise-shared-involution-forces-pairwise-marginal-closeness: that compares two context marginals through an arbitrary shared involution; this excludes a distinct literal shared word already for one row.
---

Let `a,b` be distinct literal group elements of an ordinary group `Gamma`,
with `a^2=b^2=1`.  If a projection `q in C[Gamma]` satisfies

```text
(a-b)q=0,                                               (LIM1)
```

put `g=ba`.  If `g` has infinite order, then `q=0`.  If `g` has finite order
`n`, then

```text
q<=e_g=(1/n)sum_(k=0)^(n-1)g^k,
tau_Gamma(q)<=1/n.                                     (LIM2)
```

Since `a!=b` implies `n>=2`, every nonzero literal consistency row has

```text
tau_Gamma(1-q)>=1/2.                                   (LIM3)
```

Thus a high-density rowwise Hecke-CRT certificate cannot use a distinct
literal group involution as the shared observable.  Both the context
marginals and the interpolating observable must exploit genuinely additive
group-algebra structure unless the two literal words are already equal.
