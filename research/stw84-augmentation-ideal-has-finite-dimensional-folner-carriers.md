---
rg: 2
id: stw84-augmentation-ideal-has-finite-dimensional-folner-carriers
kind: claim
title: Group-AF augmentation ideals have finite-dimensional Følner carriers
distinct_from:
  stw84-cyclic-local-finite-af-embeddable: that theorem isolates the augmentation-ideal crossed product abstractly; the present theorem constructs an explicit quasicentral approximate unit whose members lie in finite-dimensional group algebras and records the exact remaining corner obstruction.
  stw84-kernel-finite-locally-finite-by-abelian-computation: invariant finite-subgroup exhaustion supplies projection carriers fixed by the action; here the carriers are positive finite-spectrum contractions which are only asymptotically invariant, and that distinction is the unresolved seam.
artifacts:
  - research/artifacts/stw84-augmentation-folner-carriers-2026-08-30.md
---

Let `K` be a countable locally finite group, let `alpha in Aut(K)`, and put

```text
B=C*(K),       I=ker(epsilon:B->C),
J=I rtimes_alpha Z.
```

There is a quasicentral approximate unit `(h_n)` for `J` with all of the
following additional properties:

1. `h_n in I` is a positive contraction with finite spectrum;
2. `h_n` belongs to `C*(H_n)` for some finite subgroup `H_n<=K`;
3. `||alpha(h_n)-h_n|| -> 0`;
4. for every finite subset of the algebraic augmentation ideal, the sequence
   can be chosen eventually to act as the identity on both sides and commute
   with that subset.

More quantitatively, given a finite
`Omega subset C[K] intersection I` and `N>=1`, there is such an `h` with

```text
ha=ah=a                    (a in Omega),
||alpha^k(h)-h||<=|k|/N   (k in Z).                    (FAC1)
```

Let `s=1_(0,infinity)(h)`, computed in the finite-dimensional algebra
containing `h`.  Then `s in I` is a projection, `sa=as=a` for `a in Omega`,
and

```text
her_J(h)=sJs.                                             (FAC2)
```

Consequently, the cyclic core has the following exact local reduction.  If
there is a uniform `d` such that the finite-stage carrier corners `sJs`
arising above can always be chosen with

```text
dim_nuc(sJs)<=d,                                         (FAC3)
```

then

```text
dim_nuc(I rtimes_alpha Z)<=d
```

and `stw84-cyclic-local-finite-af-embeddable`
gives `dim_nuc(C*(K rtimes_alpha Z))<=d+2`.

The theorem does not claim `(FAC3)`.  The precise gap is that finite spectrum
of `h` does not give a uniform spectral gap at zero.  Although `h` is almost
`alpha`-invariant, its support projection `s` need not be almost invariant;
indeed `||alpha(s)-s||` can remain one.  Thus the positive carrier cannot be
replaced formally by an invariant finite-stage projection.
