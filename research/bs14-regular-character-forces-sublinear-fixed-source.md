---
rg: 2
id: bs14-regular-character-forces-sublinear-fixed-source
kind: claim
title: The regular BS14 character forces every inversion-compatible fixed-source carrier to have vanishing density
distinct_from:
  bs14-trivial-boundary-inversion-forces-r-fixed-source: that algebraically places the boundary source in Fix(R); this uses the regular character to show that space has asymptotically zero density.
  bs14-character-split-leaves-only-the-regular-microstate-face: that isolates the regular face abstractly; this supplies a quantitative spectral rank estimate specific to its BS generator.
  hs-spectral-counting-under-perturbation: that is a general fixed-gap counting estimate; this computes the sharp Haar quantile cost for creating a fixed sector.
---

Let `(R_n,S_n,X_n)` be a regular-character BS14-Iwahori microstate sequence,
with the BS core already exact.  The group element `R` has infinite order,
so regularity gives

```text
tr(R_n^k) ->0                    (k in Z\{0}).         (RFS1)
```

Hence the empirical spectral measures of `R_n` converge weakly to Haar
measure on the circle.  In particular

```text
dim Fix(R_n)/d_n ->0.                                (RFS2)
```

More quantitatively, suppose `V_n` is any unitary on the same space and
`alpha_n=dim Fix(V_n)/d_n ->alpha`.  Then

```text
liminf ||R_n-V_n||_2^2
 >= Phi(alpha),
Phi(alpha)=2 alpha-(2/pi) sin(pi alpha).              (RFS3)
```

For small `alpha`,

```text
Phi(alpha)=(pi^2/3) alpha^3+O(alpha^5).               (RFS4)
```

Thus creating an `alpha`-density exact fixed-source sector by an internal
core perturbation costs at least order `alpha^(3/2)` in normalized HS norm.

Now consider any exact neutral boundary dilation over the unchanged core,
with off-diagonal source block `B`.  The inversion block equation `(TBI2)`
gives

```text
ran(B) subset Fix(R_n),
rank(B)/d_n ->0.                                     (RFS5)
```

This is a regular-specific qualitative boundary-rank estimate unavailable
for arbitrary traces.  It says all ambiguity among monodromy-one source
directions is confined to `o(d)` physical rank, independently of their
possibly unbounded BS-invariant hulls.

The estimate does not itself construct the exact involution.  The even-Weil
cell shows that one fixed source can couple to a whole long packet while the
off-diagonal block still has rank one.  Therefore replacing or padding the
`o(d)` source is metrically affordable, but one must still recover the
correct global congruence atom and its two exits from the residual polar
data.  `(RFS5)` closes the positive-density source obstruction, not the
moving-level atom-authentication problem.

