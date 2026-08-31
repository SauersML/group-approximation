---
rg: 2
id: sofic-coset-action-makes-amalgam-double-sofic
kind: claim
title: A sofic coset action makes its symmetric amalgamated double sofic
distinct_from:
  gkp-free-generalized-wreath-soficity: that proves soficity of the ambient free generalized wreath product; this constructs and proves injective a canonical difference-cocycle map from the symmetric group double into that product
  kt-q2-double-hyperlinear-iff-relative-embeddable: that identifies relative embeddability with hyperlinearity for the full Kun--Thom double but does not supply it; this gives a sufficient coset-action hypothesis for soficity of any symmetric double
  one-kun-thom-compressor-is-relatively-embeddable: that is the concrete ascending-HNN application; this is the general group-theoretic mechanism for arbitrary subgroup inclusions
---

Let `Gamma subset H` be countable groups.  Assume that `H` is sofic and
that the left coset action

```text
H action X=H/Gamma
```

is a sofic action.  Then the symmetric amalgamated double

```text
D=H *_Gamma H
```

is sofic.

More precisely, put `o=Gamma`, let `F_X=*_(x in X)<z_x>` be the free
group on the coset set, and form the free generalized wreath product

```text
W=F_X rtimes H,       h z_x h^(-1)=z_(h x).
```

There is a canonical injective homomorphism

```text
D -> W                                                        (SCD1)
```

whose two vertex maps are

```text
i_0(h)=h,
i_1(h)=z_o^(-1) z_(h o) h.                                   (SCD2)
```

The maps agree on `Gamma`.  The GKP free-wreath theorem makes `W` sofic,
so its subgroup `D` is sofic.

If, in addition, there is `a in H` such that

```text
a^k notin Gamma       for every nonzero integer k,             (SCD3)
```

then `L(Gamma) subset L(H)` is relatively embeddable over the scalars
(`RE/C`).  Indeed, (SCD3) is Gao's Haar-relative-unitary hypothesis, and
the soficity above makes

```text
L(H) *_(L(Gamma)) L(H)=L(D)
```

Connes embeddable.

For the Kun--Thom pair this gives an exact firewall.  Every compressor slice
whose restricted coset action is proved sofic has a sofic double and an
`RE/C` vertex inclusion as soon as it contains one infinite-height
compressor.  The full action `G action G/Gamma` is known to be nonsofic, so
this sufficient theorem stops precisely at the multi-compressor action gate;
it asserts no converse.

DERIVATION
coset-difference-cocycle-embeds-double-proof
