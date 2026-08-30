# STW XXII: dimension-two arbitrary-factor breakthrough audit

## The theorem

For every separable-predual II1 factor `N` and compact Hausdorff space
`X` with `dim(X)<=2`, every trace on `C_sigma(X,N)` is canonical:
it is integration of the unique fibre trace against a unique probability
measure on `X`.

This crosses both previously available axes:

- Farah--Vaccaro treat arbitrary II1 fibres only through dimension one.
- The existing all-finite-dimensional theorem treats only the hyperfinite
  fibre.
- The new theorem reaches dimension two for non-McDuff factors such as
  `L(F_2)`.

## Primary-source boundary

Farah--Vaccaro, *Continuous Selection of Unitaries in II1 Factors*,
[arXiv:2501.01272v2](https://arxiv.org/abs/2501.01272), Theorems 1.1 and
1.2, prove continuous comparison and the trace theorem in dimension at most
one. Their Section 5 identifies equi-`LC^n`, rather than mere
contractibility of each unitary group, as the missing higher-dimensional
input.

Jekel, *The unitary group of a II1 factor is SOT-contractible*,
[arXiv:2508.05834](https://arxiv.org/abs/2508.05834), Theorem A, proves
SOT-contractibility for every SOT-separable II1 factor. On bounded sets the
SOT topology is the `2`-norm topology. This supplies global
one-connectedness, but not a uniform local modulus.

The already-established Cairn theorem
`stw22-diffuse-stiefel-uniform-loop-fillings` supplies precisely that
missing uniform modulus for strong Stiefel spaces. The argument below uses
no stronger consequence of Jekel's contraction.

Michael, *Continuous Selections II*, Ann. of Math. 64 (1956), Theorem 1.2,
says that a lower-semicontinuous multifunction from a space of dimension at
most `n+1`, with nonempty closed `n`-connected values forming an
equi-`LC^n` family in one complete metric space, has a continuous
selection. We use exactly `n=1`.

## New relative step

The real obstruction is not the high spectral frame. It is extending the
low spectral part of a fixed positive weight while the complement of a
chosen high-frame filling moves over a disk.

Split the low weight into dyadic bands `r_n`. At stage `n`, after the
earlier bands have been filled, the allowed target is a continuous
projection field `g_n(y)`. The original strict support inequality leaves
the same positive trace reserve

```text
tau(g_n(y))-tau(r_n) >= delta_0>0
```

at every stage.

The partial-isometry values with initial projection `r_n` and range under
`g_n(y)` are:

1. closed and nonempty;
2. lower semicontinuous by polar correction of `g_n(y)v` and a fill of
   its vanishing kernel into the trace reserve;
3. uniformly equi-`LC^1`, because they are strong Stiefel spaces in
   corners of trace at least `delta_0);
4. simply connected, by one-dimensional unitary lifting followed by
   Jekel contraction.

On the boundary of the disk, replace each value by the prescribed singleton
band frame. Lower semicontinuity survives at the boundary. Michael's theorem
then returns an exact relative extension. Recursing and taking the
orthogonal weighted sum gives the full low-spectrum extension. The tail
identity

```text
||X_M-X_N||_2^2=sum_(N<n<=M)tau(br_n)
```

makes convergence uniform and keeps the limit in the operator-norm ball.

## Weighted loop transfer

For a small loop `w` with `w^*w=a`, cut
`p_h=1_[eta,1](a)`. The high polar loop moves by at most
`eta^(-1/2)` times the weighted movement and therefore fills using the
diffuse Stiefel modulus. The new relative theorem fills the remaining
weight inside its moving complement. The low contribution costs at most

```text
2 sqrt(eta tau(supp(a))).
```

Choosing `eta` first produces one loop-filling modulus independent of
`a`. This is exactly the equi-`LC^1` input required by Michael in
dimension two. The strict target slack is never discarded.

## Trace elimination check

For a positive fibre-gap element, cut its spectrum at `epsilon`; near the
base point its support trace is below `1/(2m)`. Select one exact weighted
copy into each of `m` fixed orthogonal factor projections of trace
`1/m`. Every bounded trace `sigma` on the gap then satisfies

```text
m sigma(c) <= ||sigma||.
```

Since `m` is arbitrary, the trace vanishes. The established norm-fibre-gap
criterion gives the canonical trace formula.

## Scope and trust boundary

The theorem concerns trivial bundles and separable-predual diffuse factors.
It does not claim the same result for a nontrivial two-dimensional W-star
bundle: placing its varying Stiefel fibres into one complete ambient metric
space is a separate obstruction. It also makes no dimension-three claim;
that would require a uniform degree-two sphere-filling modulus, not merely
Jekel's nonquantitative contractibility.
