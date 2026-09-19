---
rg: 2
id: fanizza-heat-filter-one-sided-return
kind: claim
title: Return the Fanizza heat-filter sequence to one fixed carrier only in finite matrices
distinct_from:
  affine-leavitt-steinberg-hs-coefficient-decoder: that decodes a full relative Leavitt coefficient cell; this only has to return the explicit rational contraction `K_m=1-H_m`.
  single-triangle-trace-cyclic-return-cell: that targeted a native incidence chord which disappears after the Pauli reduction; this has no context holonomy and uses the game Hamiltonian directly.
---

OPEN.  Starting from the finite presentation of the two-copy native variable
group and the finite rational group-algebra contraction

```text
K_m=1-H_m,
```

construct a finite ordinary-group extension with a fixed group-algebra mark
`p_m` such that:

1. the perfect HALT representation, after countable amplification, extends
   and keeps `p_m` nonzero;
2. every finite-dimensional microstate with vanishing relator defect decodes,
   for arbitrarily large virtual depth `t`, a returned copy of `p_m` whose
   norm is bounded by a fixed loss plus `||D_R K_m^t||`;
3. the loss is independent of matrix dimension and tends to zero at fixed
   `t` with relator defect; and
4. the return is not a universal tracial equality and therefore does not
   contradict the regular representation.

By `fanizza-heat-filter-has-uniform-cstar-decay`, one may use the power bound

```text
||D_R K_m^t|| <= sqrt(C_m/(2t+1)).                    (FHR1)
```

or the preferred accelerated rational filter

```text
||D_R p_t(H_m)|| <= sqrt(C_m)/(2t).                   (FHR2)
```

Taking the microstate limit first and `t->infinity` second collapses the
fixed mark.  Exact HALT completeness uses only the ground-space identity
`K_m xi=xi` on one properly infinite representation.

The firewall is essential.  A literal group conjugacy between `p_m` and
`D_R K_m^t` would preserve norm in every representation and make the HALT
model impossible.  The return must appear only after a finite-dimensional
packet/multiplicity compression, exactly where cyclic trace or finite rank is
available.

## Minimal scalar endpoint and Toeplitz audit

The exact two-product endpoint is now
`fanizza-heat-return-is-one-cyclic-amplitude-product`.  For
`B_t=D_Rp_t(H_m)` it is enough to decode

```text
YX approximately P,
XY approximately B_t^*B_t.
```

Cyclic trace then bounds the returned projection by
`C_m/(4t^2)` plus the two decoder errors.  This is strictly more precise than
the phrase “returned copy” above and is compatible with the countably
amplified perfect model, where `B_t^*B_t=D_R`.

However `support-only-toeplitz-return-cannot-see-heat-decay` rules out the
most direct Leavitt/Toeplitz attempt.  Small operator norm does not imply
small support rank: the filtered operator may remain full-support on the
signal carrier.  Therefore a multiplicity shift which returns only its range
projection discards exactly the amplitude that `(FHR2)` controls.  The live
cell must return the amplitude square itself, or authenticate a
matrix-dependent spectral cutoff; and this inference must fail in the
regular tracial representation.

The explicit dilation audit is now complete.
`julia-dilation-packages-heat-as-one-cross-gram-moment` constructs a `2 by 2`
unitary `U_t` and equal-rank projections `E,Q_t` with

```text
E Q_t E=diag(B_t^*B_t,0).
```

Thus one projection overlap contains precisely the desired amplitude.
However `fixed-packet-julia-calculus-is-tracially-functorial` proves that
finite-packet block matrices, Julia/Halmos functional calculus and any fixed
`2 by 2` or `3 by 3` compression remain valid over arbitrary finite tracial
multiplicity algebras.  They cannot create the return `(HAP3)` without also
creating it in the regular representation.  The remaining minimum scalar is
therefore one matrix-only comparison between the fixed marked carrier and
the cross-Gram moment `tr(EQ_t)`.

This comparison is now sharpened to
`julia-authenticated-high-spectrum-rank-selector`.  It is enough to place
the normalized marked rank below the rank of

```text
1_[alpha_t,1](E Q_t E),
```

for thresholds with `alpha_t t^2->infinity`.  Markov's inequality then gives
the required decay.  `odd-clock-julia-overlap-floor-is-tracial` proves that
a literal odd cyclic clock supplies only a universal tracial overlap floor,
while `determinant-index-cannot-authenticate-julia-heat-overlap` rules out
determinant, parity and bounded Fredholm defects.  The surviving gate is an
extensive finite-coordinate Hall/conductor matching on the same marked
multiplicity reservoir.

There is now a second, potentially weaker finite-coordinate formulation.
`dimension-reported-julia-amplitude-return` uses the residual multiplicity
algebra as an Amitsur--Levitzki tape.  Its stopping index need only select a
slowly growing heat depth; it does not have to generate a supercritical
Clifford table or compare an integer index with the ambient dimension.
Moreover `one-additive-commutator-suffices-for-julia-return` reduces the
terminal payload from the two cyclic products to

```text
[Y,X] approximately P-B_t^*B_t.
```

Matrix trace then gives the heat bound directly.  The commutator has one
constant-size Steinberg root-coefficient word and, because the target is a
self-adjoint contraction, its factors may be chosen with operator norms at
most one and two uniformly in dimension.  The sole surviving issue is the
finite-coordinate decoding of that root comparison at an endogenous depth.
