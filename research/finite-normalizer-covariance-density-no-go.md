---
rg: 2
id: finite-normalizer-covariance-density-no-go
kind: claim
title: Finite automorphism covariance still loses every Schur carrier in regular residual quotients
distinct_from:
  finite-edge-attachments-residual-decouple: that treats an amalgam whose endpoint is tensor-independent; here the finite packet may act nontrivially on every old coefficient by automorphisms, so all normalizer covariance relations are present.
  packet-kazhdan-commutant-placement-decouples: that uses a direct-product packet; here the packet and the old group form a genuine semidirect product and the exact quotient representation implements the coefficient action.
  residual-action-can-erase-local-reynolds-density: that is an abstract tensor-algebra calculation; here the erasing models are left-regular representations of exact finite semidirect quotients and their old low spectrum is computed.
---

Let `Gamma=<S>` be an infinite property-`(T)` group with finite quotients of
unbounded order.  There are two possible directions for
automorphism covariance with a fixed finite packet.

First, let a fixed finite group `C` act on `Gamma` by automorphisms.  After
replacing the kernels of any unbounded quotient tower by their intersections
over `C`, there are still unbounded finite quotients `q_n:Gamma->Q_n` on
which the action descends.  Put

```text
G=Gamma semidirect C,             F_n=Q_n semidirect C.       (FAC1)
```

Inflate the left-regular representation `lambda_(F_n)` to `G`.  Its
restriction to `Gamma` is the direct sum of `|C|` copies of the regular
representation of `Q_n` (the copies may be precomposed by automorphisms and
are therefore unitarily equivalent).  Consequently

```text
dim End_Gamma(ell^2(F_n))=|C|^2 |Q_n|,
dim End_Gamma(ell^2(F_n))/|F_n|^2=1/|Q_n| -> 0.        (FAC2)
```

For a fixed inverse-closed Kazhdan set and any spectral cutoff below its
uniform gap, the old adjoint low-spectral space is exactly this commutant,
so `(FAC2)` also computes its normalized low-spectral density.

On the other hand, restriction to `C` is `|Q_n|` copies of `lambda_C`.
Thus every fixed nonzero projection `p in C[C]` has constant normalized
Hilbert mass

```text
rank(lambda_(F_n)(p))/|F_n|=rank(lambda_C(p))/|C|>0.    (FAC3)
```

More generally, for fixed subgroups `A<B<=C`, let `R_A,R_B` be their
adjoint Reynolds projections.  The normalized rank of their difference in
`End(ell^2(F_n))` is independent of `n`:

```text
rank(R_A-R_B)/|F_n|^2
 =rank(R_A^C-R_B^C)/|C|^2.                              (FAC4)
```

Hence a Schur--Clifford packet can retain fixed forbidden Hilbert mass and a
fixed positive local Reynolds density while the old property-`(T)`
commutant density tends to zero, even when the packet implements a genuine
finite automorphism action on every old coefficient.  Finite normalizer or
crossed-product covariance therefore cannot prove `(PCD1)`.  A live
coefficient cell must use covariance which does not descend to these regular
semidirect quotients--in particular the proposed one-sided Toeplitz action
must use its non-surjectivity, rather than merely the finite action induced
on its head packet.

The opposite normalizer direction fails identically.  Let `B` be a fixed
finite packet and let `Gamma` act on `B` through
`theta:Gamma->Aut(B)`.  Given any unbounded finite quotient `q_n`, replace it
by the image of

```text
Gamma -> Q_n times theta(Gamma).                            (FAC5)
```

This is still an unbounded finite quotient and `theta` factors through it.
Hence `B semidirect Q_n` is an exact finite quotient of
`B semidirect Gamma`.  Its regular representation restricts to `|B|`
copies of `lambda_(Q_n)` on the old group and `|Q_n|` copies of `lambda_B`
on the packet.  Equations `(FAC2)--(FAC4)` hold with `C` replaced by `B`.

Thus covariance in **either** finite-normalizer direction--the packet acting
on old coefficients or the old group acting on packet coefficients--retains
constant local Schur density but only `1/|Q_n|` old commutant density.  A
fixed finite packet can evade the obstruction only through a relation that
is not an automorphism crossed product, such as a genuinely non-surjective
coefficient transport.
