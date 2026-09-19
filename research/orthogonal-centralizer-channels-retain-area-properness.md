---
rg: 2
id: orthogonal-centralizer-channels-retain-area-properness
kind: claim
title: Fixed orthogonal channels retain finite-mark centralizer area properness
distinct_from:
  collective-centralizer-cycles-are-free-gauge-identities: that shows scalar cycle products erase all vertex-gauge information by free telescoping; this proves the complementary fact that retaining the errors in finitely many separate channels preserves the full twisted-Schreier obstruction.
  a5-carmichael-triangle-covers-involution-kernels: that gives a positive sum-of-squares gap for three involutions in one A5 packet; this shows that merely placing the three endpoint-correction loops in those orthogonal channels cannot make their presentation cost bounded.
  finite-mark-centralizer-commutator-area-is-proper: that treats one commutator loop; this is the fixed-multiplicity direct-sum and channel-mixing consequence needed by collective Carmichael proposals.
---

Let `G=<X|R>` be finitely presented, let `b` have finite order, fix a word
`beta` for `b`, and put `K=<b>`.  Fix `q<infinity`.  For
`h_1,...,h_q in C_G(b)`, represented by words `eta_j`, retain the `q`
commutator boundaries

```text
c_j=chain_chi([beta,eta_j])
```

in the orthogonal direct sum of the Galois local systems used by
`finite-mark-centralizer-commutator-area-is-proper`.  If this vector boundary
is expressed as a sum of `L` translated ambient relator-cell boundaries,
each sent into the `q` channels through one of a fixed finite family of
linear mixing maps, then

```text
L >= A_q sum_j d_(K\G)(K,Kh_j)-B_q                    (OCP1)
```

for constants `A_q>0,B_q>=0` depending only on the presentation, `beta`,
`q`, and the fixed mixing maps.  In particular `L` is unbounded if one of
the centralizer cosets escapes.

Thus the three channels in the `A_5` Carmichael triangle prevent the free
gauge cancellation of a scalar cycle product, but they cannot turn the
three individual endpoint-correction loops into a bounded-area collective
certificate.  A positive `A_5` return must instead attach its
sum-of-squares gap directly to the **combined Carmichael edge relations**;
it cannot obtain those relations by orthogonalizing separately filled
centralizer commutators.

The fixed-channel hypothesis is essential.  No assertion is made for a
number of channels growing with the packet or for a new relator whose local-
coefficient boundary is not the tuple `(c_1,...,c_q)`.
