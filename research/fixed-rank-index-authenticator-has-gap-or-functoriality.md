---
rg: 2
id: fixed-rank-index-authenticator-has-gap-or-functoriality
kind: claim
title: A fixed rank, index, or determinant source authenticator is either HS-discontinuous or tracially functorial
distinct_from:
  determinant-index-cannot-authenticate-julia-heat-overlap: that treats the equal-rank Julia pair and bounded defects; this gives the general fixed rectangular matrix-polynomial dichotomy and computes the compressed Fredholm index exactly.
  fixed-packet-julia-calculus-is-tracially-functorial: that treats continuous Julia calculus on one selected packet type; this identifies why adding a hard rank, kernel, index, or determinant readout does not escape unless a new uniform spectral coercivity estimate is supplied.
  fk-transfer-needs-uniform-log-integrability: that states the limit theorem for logarithmic determinants of microstates; this is a finite-coordinate source-authentication no-go and includes kernel density and rectangular index.
  extensive-cosystolic-index-defect: that asks for an unbounded family of local syndrome carriers with an energy-payment theorem; this rules out only a fixed finite matrix-polynomial detector and leaves that growing-family route open.
---

Fix integers `a,b>=1`.  For a matrix size `d`, let

```text
A_d:P_d C^(ad) -> Q_d C^(bd)                         (FRI1)
```

be a contraction, where `P_d,Q_d` are projections.  This includes every
fixed rectangular block decoded from a fixed finite packet of group words
after packet exactification.  The elementary finite-dimensional invariants
of `(FRI1)` do not supply a new normalized-Hilbert--Schmidt authentication of
the source `P_d`.

## 1. The rectangular index contains no information about the arrow

Use the intrinsic source and target spaces in `(FRI1)`.  Rank-nullity gives

```text
dim ker(A_d)-dim ker(A_d^*)
 =rank(P_d)-rank(Q_d).                                (FRI2)
```

Indeed both kernels are obtained by subtracting the same `rank(A_d)` from
the dimensions of the source and target.  Thus the normalized Fredholm index
is exactly

```text
ind(A_d)/d=tr_d(P_d)-tr_d(Q_d),                       (FRI3)
```

and is independent of the alleged source-authenticating map.  Relative
indices of projection pairs give the same trace difference whenever they
are defined.  Consequently a fixed rectangular index can only repackage the
source-versus-target rank comparison which the common-source cell already
needs; it cannot prove that the decoded source is the capacity-gated source.

## 2. Hard kernel rank is not normalized-HS continuous

There is no dimension-independent modulus controlling normalized kernel
density by normalized HS distance.  For every `d` and every `epsilon>0`,

```text
B_d=0,                  C_d=epsilon I_d
```

satisfy

```text
||B_d-C_d||_2=epsilon,
dim ker(B_d)/d=1,       dim ker(C_d)/d=0.              (FRI4)
```

Direct sum with an arbitrary spectator realizes the same jump on any fixed
positive density `alpha`.  Hence a hard kernel/rank readout cannot be bounded
by group-relator HS energy merely from a fixed polynomial evaluation's being
small.  An additional lower singular-value estimate on the purported
nonkernel is logically necessary.

## 3. Supplying a uniform spectral gap makes the detector tracial

Suppose that the extra estimate is supplied: for some fixed `gamma>0`, the
spectrum of `A_d^*A_d` avoids `(0,gamma)` throughout the small-defect regime.
Choose one continuous function `f:[0,1]->[0,1]` with

```text
f(0)=1,                 f|_[gamma,1]=0.                (FRI5)
```

Then exactly

```text
1_ker(A_d)=f(A_d^*A_d),
dim ker(A_d)/d=tr_d(f(A_d^*A_d)).                     (FRI6)
```

The right side is continuous functional calculus followed by trace.  It is
defined verbatim for the same fixed packet over every finite tracial von
Neumann multiplicity algebra.  Polynomial approximation of `f` also shows
that it is uniformly controlled by finitely many tracial moments, with a
modulus depending only on `gamma` and the fixed packet.  Thus a uniformly
gapped rank detector is not genuinely finite-dimensional; it lies inside the
tracially functorial calculus already covered by the regular-representation
firewall.

The same dichotomy holds for a fixed spectral cutoff at any threshold: with
a uniform empty band around the threshold it is continuous tracial
functional calculus, and without such a band its normalized rank can jump by
positive density under arbitrarily small normalized-HS perturbations.

## 4. Determinants have the identical split

Raw determinant phase is HS-discontinuous:

```text
Z_d=exp(i theta/d) I_d,
||Z_d-I||_2 -> 0,       det(Z_d)=exp(i theta).          (FRI7)
```

Normalized log determinant is no better at zero.  The scalar contractions
`epsilon I_d` and `epsilon^2 I_d` have HS distance at most `epsilon` while
their normalized log determinants differ by `|log epsilon|`.  If instead a
uniform lower singular-value bound `A_d^*A_d>=gamma I` is imposed, then

```text
(1/d) log |det A_d|
 = (1/2) tr_d(log(A_d^*A_d)),                          (FRI8)
```

again continuous tracial functional calculus.  Finite characters or parity
of the determinant remain discontinuous under normalized HS perturbation and
are also destroyed by amplification.

## Consequence for the capacity-gated common source

This applies directly to a proposed fixed rank/Fredholm/Hilbert-hotel backend
for `capacity-gated-common-source-gram-word-cell`.  The perfect HALT witness
has `Q=0`, so every gated rectangular arrow may still be zero; nothing here
adds an incompatible exact relation.  But a fixed rank/index/determinant
readout cannot authenticate a positive matrix source:

```text
gapless readout     => no dimension-free HS energy estimate;
uniformly gapped    => tracially functorial, hence no matrix-only return.
                                                               (FRI9)
```

Therefore the missing construction cannot be a fixed determinant line, one
Fredholm defect, or the kernel rank of one fixed block linearization.  It must
also produce a genuinely new capacity-gated spectral-coercivity/payment
theorem, or use an extensive growing family of bounded-overlap syndrome
carriers as in `extensive-cosystolic-index-defect`.  In the former case the
coercivity/payment theorem, not the rank or determinant readout, is precisely
the unresolved common-source two-cell.
