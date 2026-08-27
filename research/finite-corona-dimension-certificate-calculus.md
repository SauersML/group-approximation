---
rg: 2
id: finite-corona-dimension-certificate-calculus
kind: claim
title: Finite projection relations admit a complete rational certificate calculus in norm matrix coronas
root: true
artifacts:
  - research/finite-corona-dimension-certificate-calculus-proof.md
---

Fix stable projections `p_1,...,p_N` over a norm matrix corona `Q_d`.  A
finite projection presentation consists of relations

```text
directSum_i p_i^(directSum L_(a,i))
  ~MvN
directSum_i p_i^(directSum R_(a,i))                    (FDC1)
```

for `1<=a<=k`, where `L,R` are nonnegative integer matrices.  Put

```text
B=L-R in M_(k x N)(Z),
C_B={x in R_(>=0)^N : Bx=0}.                           (FDC2)
```

Then the following are equivalent for a marked coordinate `i`:

1. every realization of `(FDC1)` in every norm matrix corona has `p_i=0`;
2. every `x in C_B` has `x_i=0`;
3. there are `y in Q^k` and `s in Q_(>=0)^N` such that

   ```text
   -e_i=B^T y+s.                                       (FDC3)
   ```

Thus universal vanishing forced by a finite list of stable projection
relations has a finite rational certificate.  The certificate is checked by
exact rational arithmetic and is complete for consequences of the listed
dimension relations.

If `(FDC3)` does not exist, then `C_B` contains a rational vector with
positive `i`-th coordinate.  Clearing denominators gives a nonnegative
integer rank assignment satisfying every relation in `(FDC1)` and keeping
the marked coordinate nonzero.  Consequently the listed dimension relations
alone cannot prove that `p_i` vanishes.

The calculus has exact finite operations:

* adjoining a projection relation intersects the current rational cone with
  one rational hyperplane;
* adjoining auxiliary projections and then forgetting them projects a
  rational polyhedral cone;
* independent presentations combine by block sum;
* substitution of one finite branching presentation into another multiplies
  their incidence matrices;
* iteration of an `A`-branching presentation replaces `A` by `A^n` without
  changing the represented projections.

For a finite-order marked element `z` in a countable group, include its
active spectral projection among the `p_i`.  Any certificate `(FDC3)` for
that coordinate proves `z in Rad_MF(G)`.  If the marked elements whose active
projections are certified normally generate `G`, then `Rad_MF(G)=G`.

The same finite program applies to isotypic projections of finite group
packets.  Fourier decompositions, restriction multiplicities, conjugacy, and
partial-isometry relations all become integer rows of `B`; one rational dual
certificate then annihilates the selected nontrivial spectral types in every
norm-corona representation.
