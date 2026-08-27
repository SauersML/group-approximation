---
rg: 2
id: correlated-haar-onehot-dichotomy
kind: claim
title: Correlated Haar one-hot selectors either remain affine-small or are the full algebraic-envelope problem
distinct_from:
  finite-one-hot-algebraic-corners-reduce-to-stabilizers: that computes a single finite one-hot orbit with no residual fiber; this allows an arbitrary correlated linear subshift, computes all finite marginal densities, and retains the possible infinite nonlinear corner.
  one-hot-selector-parity-barrier: that excludes exact one-hot solution sets of affine equations; this also treats positive-density nonlinear conditioning of Haar measure and identifies the surviving crossed-product corner.
  finite-field-haarization-survival-dichotomy: that studies affine masking and recovery of an existing source law; this starts from Haar measure and asks whether correlated selector conditioning creates the missing nonlinear holonomy.
---

Let `p` be prime, let `Q` be a finite label set of size `m>=3`, and let

```text
K <= (F_p^Q)^I
```

be a closed linear subshift with Haar probability `mu`.  Put
`H_Q={e_q:q in Q}`.  For finite `F subset I`, write `K_F=pi_F(K)` and

```text
Y_F={x in K: x_i in H_Q for every i in F}.
```

Then the complete finite-marginal density formula is

```text
mu(Y_F)=|K_F intersect H_Q^F|/|K_F|.                 (CHO1)
```

In particular, if `r_F=dim_(F_p) K_F`, then

```text
mu(Y_F) <= m^|F| p^(-r_F).                           (CHO2)
```

Thus LDPC distance or local testability alone does not preserve selector
density.  A linear code with
`r_F >= (log_p(m)+eta)|F|` has exponentially vanishing all-one-hot density.
Conversely a repetition/diagonal code can have maximal relative distance and
constant selector density, so distance cannot improve `(CHO2)`; it merely
moves the selector entropy into a low-dimensional correlated factor.

There are exactly two rigorous outcomes for the infinite one-hot locus

```text
Y=intersection_(i in I) Y_{ {i} }.
```

1. If its normalized conditional law is invariant affine Haar, then every
   one-coordinate marginal is an affine subspace contained in `H_Q`.  Such a
   marginal has size at most two when `p=2`, and size one when `p` is odd.
   Hence an affine-Haar component cannot carry a genuine `m>=3` selector.
   Good linear-code correlations do not evade the affine control-flow
   barrier.

2. If `mu(Y)>0`, `Y` is invariant under an automorphic action of `Lambda`,
   and the conditional law on `Y` is genuinely nonlinear, then, for
   `M=L^infinity(K) rtimes Lambda` and `z=1_Y`,

   ```text
   zMz = L^infinity(Y,mu(Y)^(-1)mu|Y) rtimes Lambda.  (CHO3)
   ```

   The projection `z` is central.  Therefore a non-Connes-embeddable BCS
   holonomy in this corner already makes `M` non-CE and, by Pontryagin
   duality, makes `K-hat rtimes Lambda` non-hyperlinear.  This is a valid
   survivor, but it is exactly the algebraic compact-action envelope itself;
   correlations have not supplied a cheaper trace-promotion step.

There is a further finite-image reduction.  If the selector-name map on `Y`
has finite `Lambda`-invariant image `Omega`, then for orbit representatives
`omega` and `H_omega=Stab_Lambda(omega)`,

```text
zMz ~= direct_sum_[omega in Omega/Lambda]
          M_|Lambda omega|(L^infinity(Y_omega) rtimes H_omega).   (CHO4)
```

Consequently any non-CE data already lies in a stabilizer **fiber action**.
When the fibers are points this is precisely the earlier point-stabilizer
theorem.  A genuinely new correlated-Haar construction must therefore have
an infinite selector-name image and must prove non-CE of its nonlinear
positive corner -- the original envelope obligation.  Finite correlated
registers, diagonal repetition, and ordinary good-LDPC correlations do not
escape this dichotomy.

