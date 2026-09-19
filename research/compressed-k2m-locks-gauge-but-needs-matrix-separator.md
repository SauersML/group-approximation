---
rg: 2
id: compressed-k2m-locks-gauge-but-needs-matrix-separator
kind: claim
title: Compressed K2,m rectangles lock the last gauge but still need a matrix-only separator
distinct_from:
  unitary-k2m-rectangle-synchronization: that gives exact row-column factorization of uncompressed unitary edge data; this adds orthogonal source cuts and a smaller target capacity and proves the resulting quantitative rank-deficit inequality.
  one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum: that leaves one last edge gauge free around a single cycle; the rectangle family removes that gauge and identifies the compressed leakage scalar which remains unavailable to universal word relations.
  shared-bcs-eight-slice-full-overlap-actuator: that asks for one almost-full source-to-capacity overlap from the shared BCS; this shows how rectangle synchronization would aggregate columnwise compressed returns once such a matrix-only overlap/leakage estimate is supplied.
---

**ESTABLISHED ANALYTIC CELL AND SHARP INTERFACE.** Let `m>=2`, let

```text
M_(i,j) in U(d),             i in {0,1}, 0<=j<m,
G_j projections,            C a projection.             (CKR1)
```

Define the rectangle holonomies

```text
H_j=M_(1,j)M_(0,j)^*M_(0,0)M_(1,0)^*,       1<=j<m,    (CKR2)
h=sum_(j=1)^(m-1)||H_j-I||_2^2,                         (CKR3)
ell=sum_j||(I-C)M_(1,j)G_j||_2^2.                       (CKR4)
```

Assume the row-zero source ranges

```text
M_(0,j)G_jM_(0,j)^*                                   (CKR5)
```

are pairwise orthogonal. Then

```text
tr(sum_j G_j)-tr(C) <= (sqrt(ell)+sqrt(h))^2
                     <=2(ell+h).                       (CKR6)
```

Thus the `m-1` rectangles remove the final column gauge exactly. A positive
source-capacity deficit must appear either in an ordinary rectangle word or
in a **compressed row-one leakage**.

## Proof

Apply `unitary-k2m-rectangle-synchronization`. There are unitaries
`A_0,A_1,B_j` such that

```text
M_(0,j)=A_0B_j,
M_(1,0)=A_1B_0,
sum_j||M_(1,j)-A_1B_j||_2^2=h.                         (CKR7)
```

Put `S_j=B_jG_jB_j^*`. By `(CKR5)` the `S_j` are orthogonal, so
`S=sum_j S_j` is a projection. Capacity gives

```text
sum_j||(I-C)A_1B_jG_j||_2^2
 =tr(S)-tr(CA_1SA_1^*)
 >=tr(S)-tr(C)
 =tr(sum_jG_j)-tr(C).                                  (CKR8)
```

Regard the `m` compressed operators as one vector in the Hilbert direct sum
of `m` matrix Hilbert spaces. The triangle inequality and `(CKR7)` give

```text
(sum_j||(I-C)A_1B_jG_j||_2^2)^(1/2)
 <=sqrt(ell)+sqrt(h),                                  (CKR9)
```

which proves `(CKR6)`.

## Eight-slice specialization

Take `m=3`, let the `G_j` be the three orthogonal equalized failures from
`eight-slice-bookkeeping-symmetrizes-s3-failures`, and let `C` be its parent
slice. Then

```text
tr(sum_jG_j)-tr(C)=tr(P_f)/16.                         (CKR10)
```

Consequently rectangle word energy plus a shared-BCS estimate

```text
ell<=K_sep E_rel+o(1)                                  (CKR11)
```

would give the return payment required in `(SBR3)`. This replaces one closed
cycle by two independent rectangles and genuinely prevents the last-edge
assignment used in `(HHC4)`.

## Why the rectangles alone still fail

Set `M_(i,j)=A_iB_j` with arbitrary row and column unitaries and choose the
`B_jG_jB_j^*` orthogonal. Every rectangle holonomy is exactly the identity,
while `(CKR10)` remains positive. Hence no inequality charging the capacity
deficit to `h` alone is possible, no matter how many uncompressed squares are
added.

Nor can `(CKR11)` be supplied by literal universal conjugacy relators between
the source and capacity reflections while the finite packet embeds. If
`R_C=I-2C` and `R_(G,j)=I-2G_j` were literal packet words, then

```text
r_j=R_C M_(1,j)R_(G,j)M_(1,j)^*
```

satisfies

```text
||(I-C)M_(1,j)G_j||_2^2<=1/4||r_j-I||_2^2.            (CKR12)
```

Making every `r_j` a defining relator would set `ell=h=0` in the canonical
regular representation, contradicting `(CKR6)` whenever the finite packet
has positive forbidden mass. The same firewall applies to controlled-swap
versions whose compressed inequality is valid in every representation.

Therefore the rectangle cell solves **gauge synchronization**, not the
Connes-embedding separation. A positive ordinary-group compiler must make
`(CKR11)` hold only for finite matrix microstates by consuming moments of the
original shared non-CE BCS tuple. This is precisely the matrix-only
compressed two-cell left by GTC4; finite packet squares cannot manufacture
it.

## Finite-phase Fourier test

`fourier-normalizer-words-control-block-gram-leakage` gives a new exact test
for the residual interface.  If the source and capacity cuts in `(CKR4)` can
be embedded into a finite spectral partition for a phase word `D`, the
ordinary words

```text
[P D^r P^*,D],                 1<=r<m,
```

exactly dominate every off-type block-Gram product of `P`.  Several phase
tags arranged as an error-correcting code weight every pair of distinct
types by a fixed positive amount.  Thus the Fourier words kill the
cross-type Gram part of the compressed leakage once the analytic cuts have
been authenticated.

They do not by themselves control the scalar `ell`.  As
`normalizer-phase-tests-leave-diagonal-type-transport` makes explicit, the
Fourier commutators vanish when a source block is transported wholly into a
wrong target phase: they see cross-block coherence, not diagonal type
population.

The exact scalar reduction is instead
`compressed-k2m-deficit-is-one-aggregate-sign-row`.  If
`S=sum_jB_jG_jB_j^*`, then the whole synchronized leakage is paid by the one
binary covariance row between `I-2S` and `I-2C`.  Hence the remaining task is
sharper than a general Gram separator: `finite-phase-tags-authenticate-forbidden-cuts`
must authenticate the aggregate source and capacity signs and derive their
**phase-matching covariance** from the shared BCS tuple only in finite
canonical microstates.  Declaring those noncanonical cuts or the covariance
as universal packet relations still hits the regular-trace firewall.
