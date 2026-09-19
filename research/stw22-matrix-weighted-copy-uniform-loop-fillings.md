---
rg: 2
id: stw22-matrix-weighted-copy-uniform-loop-fillings
kind: claim
title: Matrix weighted-copy fibres have a dimension-free uniform loop-filling modulus
distinct_from:
  stw22-multicopy-fibres-collapse-and-zero-slack-obstructs-lc1: that theorem gives the exact Stiefel reduction and the zero-slack obstruction in every finite factor; the present theorem proves the missing dimension-free positive-slack estimate for all matrix factors and transfers it to positive weights.
  stw22-weighted-equi-lc1-reduces-to-unweighted-stiefel-filling: that theorem treats one weighted copy in the hyperfinite II_1 factor using the Popa--Takesaki contraction; the present theorem treats arbitrary finite matrix factors and arbitrary replication number by finite-dimensional defect localization.
  stw22-dim1-factor-bundles-have-uniform-traces: that theorem needs only uniform local path connectedness for arbitrary finite-factor fibres; the present theorem supplies the next local-connectivity degree for the matrix-fibre subfamily.
artifacts:
  - research/artifacts/stw22-matrix-weighted-loop-filling-audit-2026-08-30.md
---

Equip every matrix algebra `M_n` with its normalized trace and every finite
tuple with the Hilbert-sum `2`-metric. Fix `m>=1` and `gamma>0`. For a
positive contraction `a in M_n` satisfying

```text
m tau(supp(a)) <= 1-gamma,
```

let

```text
F_(n,m)(a)={ (v_1,...,v_m):
             v_j^*v_j=a and the v_jv_j^* are pairwise orthogonal }.
```

There is a modulus independent of `n,m,gamma`, and `a`: if
`epsilon_0=min(epsilon,1)`, one may take

```text
rho(epsilon)=epsilon_0^3/276480.
```

Every continuous loop in one `F_(n,m)(a)` whose image lies in a
`rho(epsilon)`-ball about one of its points has a continuous filling in the
concentric `epsilon`-ball.

The projection-weight core is stronger. If `q` is any proper projection in
`M_n`, then

```text
St_n(q)={v in M_n:v^*v=q}
```

has the same property with the universal quadratic modulus

```text
rho_St(epsilon)=min(epsilon,1)^2/2560.
```

No quantitative lower bound on `tau(1-q)` is needed; only `q!=1` is needed.
This is sharp at the endpoint: for `q=1`, determinant winding loops in
`U(n)` can have arbitrarily small normalized `2`-diameter as `n` grows and
are not null-homotopic.

The proof in this node is only a matrix-fibre argument.  The separate
summable-carrier theorem `stw22-diffuse-stiefel-uniform-loop-fillings`
supplies the projection-weight input in every separable `II_1` factor, and
`stw22-all-finite-factor-weighted-copy-uniform-loop-fillings` supplies the
unitary-lifted low-spectrum recursion which upgrades it to arbitrary
positive weights.
