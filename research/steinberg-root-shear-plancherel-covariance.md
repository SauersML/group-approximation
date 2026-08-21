---
rg: 2
id: steinberg-root-shear-plancherel-covariance
kind: claim
title: Canonical Steinberg root windows have Plancherel Fourier blocks and exact shear permutations
distinct_from:
  near-regular-finite-character-fixes-plancherel-types: that treats an arbitrary fixed finite group after exactification; this identifies the concrete finite row-root subgroup and computes the Steinberg multiplication shear on its Fourier labels.
  hs-steinberg-root-kernel-is-linear-sofic: that asks for one compatible rank-ultraproduct model of the entire coefficient quotient; this is a fixed-window theorem whose constants may depend on the chosen coefficient spaces.
  carrier-not-decoder: that gives one finite countermodel showing a common long-root carrier is insufficient; this proves the positive Plancherel/covariance statement available on every finite Steinberg row-root window.
---

Let `R` be an associative algebra of characteristic `p`, let `m>=3`, and
work in `St_m(R)`.  Fix finite-dimensional `F_p`-subspaces `V,W subset R`
and `r in R` such that

```text
V r subset W.                                             (PSH1)
```

The same-row root subgroup

```text
H_(V,W)={x_12(a)x_13(c):a in V, c in W}                  (PSH2)
```

is canonically the finite elementary abelian group `V direct_sum W`.
Writing `q_r=x_23(r)`, the Steinberg relations give

```text
q_r^-1 x_12(a)x_13(c) q_r
  =x_12(a)x_13(c+ar).                                    (PSH3)
```

Thus `q_r` normalizes `H_(V,W)` by the linear shear

```text
alpha_r(a,c)=(a,c+ar).                                   (PSH4)
```

Now let `U_n` be normalized-Hilbert--Schmidt microstates on a fixed word
window containing the complete multiplication table of `H_(V,W)`, `q_r`,
and `(PSH3)`.  Assume their defects on that window tend to zero and their
normalized traces have the canonical delta profile on `H_(V,W)`:

```text
tr(U_n(h))->0                 for h!=1 in H_(V,W).        (PSH5)
```

For `theta in dual(H_(V,W))`, form the Fourier operator

```text
e_(theta,n)=|H_(V,W)|^-1 sum_(h in H_(V,W))
                 conjugate(theta(h)) U_n(h).             (PSH6)
```

Then the finite family `(e_(theta,n))_theta` is an `o(1)` orthogonal PVM in
normalized HS norm,

```text
tr(e_(theta,n))->1/|H_(V,W)|,                            (PSH7)
```

and the shear covariance is

```text
||U_n(q_r)^* e_(theta,n) U_n(q_r)
       -e_(theta compose alpha_r^-1,n)||_2 ->0.           (PSH8)
```

All losses are dimension-independent for the fixed spaces `V,W`; they are
finite sums of the word defects on the displayed table.  Equivalently, after
flexible finite-group exactification, every Fourier block has asymptotic
Plancherel density and `q_r` transports the exact blocks by the permutation
dual to `(PSH4)` up to `o(1)` HS error.

This gives the canonical finite-window substrate for the affine Leavitt
decoder: right multiplication by each named coefficient is visible as an
explicit permutation of equal-density row-root Fourier blocks.  It does not
assemble the windows into a coefficient quotient and does not yet turn their
boundary into the contractions required by `(ALD1)`.
