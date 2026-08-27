---
rg: 2
id: signed-character-expansion-decodes-operator-parallelograms
kind: claim
title: Signed-character expansion decodes operator parallelograms to one affine PVM
distinct_from:
  expander-edge-overlay-detects-simplex-exterior-square: that samples decomposable wedges after a global code section exists; this constructs the global commuting affine table from local four-point operator relations.
  bounded-template-average-blr-occurrence-decoder: that needs a growing-dimensional simplex/PCPP family; this theorem applies to the affine-character code of a left-right Cayley square complex.
---

ESTABLISHED.  Let `G_i` be finite groups with symmetric generating sets
`A_i,B_i` of uniformly bounded size and satisfying total no-conjugacy, so

```text
[a,g,b]={g,ag,gb,agb}                                      (SCE1)
```

has four distinct vertices.  Assume:

1. the right Cayley graphs `Cay(G_i,B_i)` have a uniform spectral gap; and
2. the left labeled Cayley graphs have a uniform **signed-character gap**:
   for every inverse-consistent sign pattern
   `sigma:A_i->{+1,-1}` and every Hilbert-valued `F` on `G_i`,

```text
dist(F,K_sigma)^2
 <= kappa^(-1) E_(g,a)||F(ag)-sigma(a)F(g)||^2,             (SCE2)
```

   where `K_sigma={g |-> chi(g)v}` if `sigma` extends to a character
   `chi:G_i->{+1,-1}`, and `K_sigma=0` otherwise.  The constant `kappa>0`
   is independent of `i` and of the coefficient Hilbert space.

For reflections `Q_g in M_d(C)`, let `epsilon_square(Q)` be the average over
`(g,a,b)` of the squared normalized Hilbert--Schmidt parity defect

```text
||Q_g Q_(ag) Q_(gb) Q_(agb)-I||_2^2                       (SCE3)
```

plus the six squared commutator defects between the four entries of `(SCE1)`.
There is a modulus `omega(t)->0`, depending only on the two gaps and the
degree bounds, such that

```text
inf E_g ||Q_g-Q'_g||_2^2 <= omega(epsilon_square(Q)),       (SCE4)
```

where the infimum is over global affine PVM tables

```text
Q'_g = sum_(chi,c) (-1)^(chi(g)+c) E_(chi,c),               (SCE5)
```

and `{E_(chi,c)}` is one PVM on the same matrix algebra.  In particular all
`Q'_g` commute.  The modulus is uniform in `|G_i|` and `d`; the proof is a
tracial compactness argument, so no linear rate is asserted.

This is the exact operator-cosystolic inequality sought for the bare
left-right parallelogram test.  The signed gap, not ordinary expansion alone,
is load-bearing: it excludes almost-eigenfunctions for inconsistent generator
signs and identifies the valid eigenspaces with actual group characters.
