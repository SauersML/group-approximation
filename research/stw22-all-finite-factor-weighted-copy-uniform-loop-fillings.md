---
rg: 2
id: stw22-all-finite-factor-weighted-copy-uniform-loop-fillings
kind: claim
title: Strictly slack weighted-copy fibres have one loop-filling modulus in all finite factors
distinct_from:
  stw22-matrix-weighted-copy-uniform-loop-fillings: that theorem proves the matrix case; the present theorem also treats every separable II_1 factor by a unitary-lifted spectral-band recursion.
  stw22-diffuse-stiefel-uniform-loop-fillings: that theorem treats only projection weights in diffuse factors; the present theorem proves the missing relative extension for arbitrary positive weights.
  stw22-low-spectrum-weighted-boundary-filling: that theorem works in the hyperfinite factor and every sphere degree; the present theorem works in every separable finite factor but only for loops.
artifacts:
  - research/artifacts/stw22-diffuse-weighted-loop-extension-audit-2026-08-30.md
---

Let `(N,tau)` be either a normalized matrix factor or a `II_1` factor with
separable predual.  Equip finite tuples with the Hilbert-sum `2`-metric.
Fix `m>=1`, `gamma>0`, and a positive contraction `a in N` satisfying

```text
m tau(supp(a)) <= 1-gamma.
```

For

```text
F_(N,m)(a)={ (v_1,...,v_m):
              v_j^*v_j=a and the v_jv_j^* are pairwise orthogonal },
```

put `epsilon_0=min(epsilon,1)`.  Every continuous loop in one
`F_(N,m)(a)` contained in the ball of radius

```text
rho(epsilon)=epsilon_0^3/276480
```

about a point of that fibre has a continuous filling in the concentric
`epsilon`-ball.  The modulus is independent of `N,m,gamma`, and `a`.
Moreover every loop in every such fibre is null-homotopic.

The strict support slack is qualitative only.  It guarantees that every
finite spectral-band frame has a nonzero complementary corner, but it does
not enter the modulus.  It cannot be omitted uniformly: projection weights
with zero slack include the determinant-winding obstruction in matrix
unitary groups.

The new relative statement used in the proof is also exact.  Suppose a
high-frame filling over `D^2` has a continuous unitary trivialization of
its range complement.  Any boundary low-weight `m`-frame, with fixed
positive weight `b` and with strict unused trace after all `m` copies, has
an extension inside that moving complement.  The extension is obtained by
bounded spectral bands of `b`; no polar frame on `supp(b)` is selected or
asserted continuous.
